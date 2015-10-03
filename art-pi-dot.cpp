/*------------------------------------------------------------------------
 *
 *  Famake's Art-Net -> DotStar SPI gateway
 *
 *
 * Based on Adafruit DotStar Raspberry Pi lib 
 * (https://github.com/adafruit/Adafruit_DotStar_Pi)
 *
 * Art-Net interface for the DotStar LED strips. Supports a minimal 
 * subset of the Art-Net protocol, needed to push pixels to the strips.
 * The rationale for choosing Art-Net is that it is already a (de facto)
 * standard for lighting control, and the LED strips become available to
 * applications such as Madrix (http://www.madrix.com/).
 *
 * This code ditches the Python interface and works with C only, it also
 * does not support bit-banging. It's written in C, but using many 
 * features from C++, so it won't compile in C-only mode.
 *
 * 	-- Functional overview --
 * 
 *  There are two phases: 
 *    - Collect data for a frame
 *    - Send data on SPI
 *
 *  The sync. algorithm is described below. 
 *
 * The code is licensed under the GNU Lesser General Public License.
 * See the Adafruit library for details.
 *------------------------------------------------------------------------*/

#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <sys/mman.h>
#include <sys/ioctl.h>
#include <linux/spi/spidev.h>
#include <string.h>
#include <arpa/inet.h>
#include <sys/socket.h>


// Configuring the Art-Net universes. Art-Net has a hierarchical 
// address space. The lowest level is the channel, representing for
// us a colour channel of a pixel. 512 channels are adressable in 
// each universe (corresponding to DMX, which also has 512 channels).
// 32768 universes are supported. We only use 510 channels per universe,
// as this corresponds to the largest number of complete RGB LEDs 
// possible (170).


/*
 * Synchronization algorithm (v0)
 *
 * ** Assumptions **
 *
 * Updates are divided into frames, which contain values for
 * all pixels. By necessity, if there is more than 170 pixels, the frame
 * spans multiple Art-Net universes, and thus multiple UDP
 * datagrams. The data in a frame is sent in a burst, so there is a much
 * shorter interval between the packets of a single frame than between 
 * packets in different frames. The SPI interface is not fast enough
 * to push a full frame every time a packet (partial frame) is received,
 * so we must collect full frames before sending to SPI.
 *
 * The packets aren't expected to arrive in order. This makes the 
 * algorithm more complex, but I have no reason to believe that all
 * software sends universes in any particular order.
 *
 * Universe     |--------------- time  ------------------|
 * 1              d               d             d
 * 2               d              d              d
 * 3             d                 d            d
 * 4                d             d              d
 *  
 *  (d = datagram)
 * 
 * Dropped packets must be expected. The main challenge is regaining 
 * synchronization after one or more packets of a frame have been lost.
 * There is no way to per se identify a packet as belonging to a 
 * particular frame. While Art-Net does specify a "sequence number"
 * field, this is not used by the Madrix software, so I have to assume
 * that it's not commonly used and I can't make use of it.
 *
 * The frame rate is not known in advance, but frames are assumed to 
 * be sent at a fixed rate over reasonably long periods (as if it's a
 * config parameter of the sending process).
 * 
 *
 * ** Design goals **
 *
 * - The algorithm  shouldn't introduce dropped frames or jitter 
 *   under optimal network conditions.
 * - Should use a small amount of computing resources and be quick
 *   (don't care too much about memory efficiency).
 * - Should regain sync quickly when faced with a moderate packet
 *   loss.
 *
 *
 * ** Definition of the algorithm **
 * 
 * The basis is to record when each universe packet arrives, and send
 * a frame when all have arrived. A flag is kept for each universe to 
 * detect whether it has arrived.
 *
 * The time of arrival of each packet is recorded. When a full frame is
 * received, the time between the first and the last packet of the 
 * frame is computed.
 *
 * After each packet is received, the time between the least recently 
 * arrived packet and the current packet is computed. If this is less
 * than a third of the last full frame time (as in the previous paragraph),
 * the current data are considered a full frame, sent to SPI, and 
 * all universe arrival flags are reset (some were never set, though).
 * If this condition is never met for a frame (the normal case), the
 * frame is sent when all universes have arrived.
 *
 * The above is the primary synchronization mechanism. Schematically,
 * a dropped packet is handled like this:
 *
 *                            dropped packet
 *                            v
 * Universe     |--------------- time  ------------------|
 * 1             d          d          d             d
 * 2              d          d         ^d             d
 * 3               d                   | d             d
 * 4                d          d       |  d             d
 *                  ^                  | ^^
 *                  | Full frame 1     | ||
 *                  |== frame duration ==|Full frame 2
 *                                     |  |
 *                                     |==| Condition triggered
 *                                          additional frame sent
 *
 * A secondary mechanism is to drop frames which are likely to be from
 * two different true frames, such as the second full frame in the 
 * above example. If the full frame time exceeds three times the
 * previous full frame time, the frame is recorded as normal, but not
 * sent to SPI.
 *
 * ** Edge cases **
 *
 * When the frame rate gets close to the rate at which one can push 
 * frames over SPI, the behaviour is unpredictable. Have to make a 
 * multithreaded version then.  
 *
 */

#define ARTNET_PORT 0x1936


// Settings
#define NUM_PIXELS 200
#define START_UNIVERSE 0

#define ARTNET_BYTES_PER_UNIVERSE 510
#define OUTPUT_BYTES_PER_UNIVERSE 510*4/3



#define DEBUG 1
#define DBG(msg) if(DEBUG) printf("[%03d] %s\n", (int)(clock() % 1000), msg); 


// Precompute some useful constants based on the settings
const int num_universes = (NUM_PIXELS + 169) / 170;
const int num_complete_universes = NUM_PIXELS / 170;
const int last_universe = START_UNIVERSE + num_universes - 1;
const int pixels_in_last_universe = NUM_PIXELS - (num_universes-1) * 170;

const uint32_t bitrate = 32000000; // bps

uint8_t* output_buffer;
uint32_t* arrival_time; // using a cheeky 32 bit int for time
uint32_t last_frame_time;
bool* arrival_flag;

int startup = 3;

int fd;

// SPI transfer operation setup.  These are used w/hardware SP.
static uint8_t header[] = { 0x00, 0x00, 0x00, 0x00 },
               footer[] = { 0xFF, 0xFF, 0xFF, 0xFF };
static struct spi_ioc_transfer xfer[3];

uint32_t get_first_arrival() {
	uint32_t min = arrival_time[0];
	for (int i=1; i<num_universes; ++i)
		if (arrival_time[i] < min)
			min = arrival_time[i];
	return min;
}

void mark_frame_sent(uint32_t first_arrival) {
	int i;
	for (i=0; i<num_universes; ++i) {
		arrival_flag[i] = false;
	}
	uint32_t frame_time = ((uint32_t)clock() - first_arrival);
	last_frame_time = frame_time;
}

int do_output() {
	// All that spi_ioc_transfer struct stuff earlier in
	// the code is so we can use this single ioctl to concat
	// the header/data/footer into one operation:
	(void)ioctl(fd, SPI_IOC_MESSAGE(3), xfer);
}

void check_do_led_output(int universe) {
	int i_universe = universe - START_UNIVERSE;
	uint32_t time = (uint32_t)clock();
	arrival_flag[i_universe] = true;

	bool all_arrived = arrival_flag[0];
	int i;
	for (i=1; all_arrived && i<num_universes; ++i)
		all_arrived = arrival_flag[i];

	uint32_t first_arrival = get_first_arrival();
	uint32_t frame_time = (uint32_t)(clock() - first_arrival);

	if (all_arrived) { // All universes arrived!
		DBG("All have arrived, sending");
		if (frame_time * 3 < last_frame_time) {
			do_output();
		}
		mark_frame_sent(first_arrival);
	}
	else {
		if (frame_time * 3 < last_frame_time) {
			DBG("Sending the packet even though not all arrived!");
			do_output();
			mark_frame_sent(first_arrival);
		}
	}
}

// Process a packet. Returns true in most cases, false on fatal errors.
bool process_packet(int packet_length, const uint8_t* buffer) {
	
	if (packet_length <= 18) {
		DBG("Too small packet");
		return true;
	}
	uint16_t universe = *(const uint16_t*)(buffer + 14);
	//uint16_t length = *(uint16_t*)(buffer + 16);
	uint16_t length = buffer[17] | (((uint16_t)buffer[16]) << 8);

	// Skip packet if things don't add up
	if (universe < START_UNIVERSE || universe > last_universe) {
		DBG("Not our universe received");
		return true;
	}
	if (universe == last_universe) {
		if (length != pixels_in_last_universe*3) {
			DBG("Invalid number of pixels received");
			printf("Got %d data\n", length);
			return true;
		}
	}
	else {
		if (length != ARTNET_BYTES_PER_UNIVERSE) {
			DBG("Invalid number of pixels received");
			return true;
		}
	}

	if (packet_length < length + 18) {
		DBG("Actual packet length shorter than specified length");
	}

	DBG("Received a valid packet!");
	// Accept it without checking more headers
	//
	int output_index = universe * OUTPUT_BYTES_PER_UNIVERSE;
	int input_index = 18;
	int i;

	for (i=0; i<length; i+=3, input_index+=3, output_index+=4) {
		output_buffer[output_index+1] = buffer[input_index+2]; // B <- B
		output_buffer[output_index+2] = buffer[input_index+1]; // G <- G
		output_buffer[output_index+3] = buffer[input_index];   // R <- R
	}

	// Send to LED strip now if required
	check_do_led_output(universe);
	return true;
}


bool receiver() {
  int s;
	if ((s = socket(AF_INET, SOCK_DGRAM, IPPROTO_UDP)) == -1) {
    perror("socket");
		return false;
	}

	struct sockaddr_in si_me;
	memset((char *) &si_me, 0, sizeof(si_me));
	si_me.sin_family = AF_INET;
	si_me.sin_port = htons(ARTNET_PORT);
	si_me.sin_addr.s_addr = htonl(INADDR_ANY);
     
	if (bind(s, (struct sockaddr*)&si_me, sizeof(si_me)) == -1) {
    perror("bind");
		return false;
	}

	
	uint8_t buffer[1024];
	ssize_t len;
	while(true) {
		if ((len = recv(s, buffer, sizeof(buffer), 0)) == -1) 
			return false;
		
			if (!process_packet(len, buffer)) 
				return false;
	}
  
}


bool init() {
	int i;

	// Initialize buffers and data structures
	arrival_time = (uint32_t*)malloc(num_universes * sizeof(uint32_t));
	arrival_flag = (bool*)malloc(num_universes * sizeof(bool));

	// Set up SPI
	if((fd = open("/dev/spidev0.0", O_RDWR)) < 0) {
		printf("Can't open /dev/spidev0.0 (try 'sudo')\n");
		return false;
	}
	// Mode=0 and no chipselect copied from Adafruit's code
	uint8_t mode = SPI_MODE_0 | SPI_NO_CS;
	ioctl(fd, SPI_IOC_WR_MODE, &mode);
	// Speed!
	ioctl(fd, SPI_IOC_WR_MAX_SPEED_HZ, bitrate);

	// Set up buffer
	const int buffer_size = NUM_PIXELS*4;
	output_buffer = (uint8_t*)malloc(buffer_size);
	if (output_buffer == NULL) {
		printf("Unable to allocate buffer (not enough memory?)\n");
		return false;
	}
	// Initialize to black (leading byte must always be 0xFF, three next
	// bytes are the colours, set to black.
	for (i=0; i<buffer_size; i+=4) {
		output_buffer[i] = 0xFF;
		output_buffer[i+1] = 0;
		output_buffer[i+2] = 0;
		output_buffer[i+3] = 0;
	}

	// Set up SPI output data structures
	memset((char*) xfer, 0, sizeof(xfer));
	for (i=0; i<3; ++i) {
		xfer[i].rx_buf = 0;
		xfer[i].delay_usecs = 0;
		xfer[i].bits_per_word = 8;
		xfer[i].cs_change = 0;
		xfer[i].speed_hz = bitrate;
	}

	xfer[0].tx_buf = (unsigned long)header;
	xfer[1].tx_buf = (unsigned long)output_buffer;
	xfer[2].tx_buf = (unsigned long)footer;
	xfer[0].len = sizeof(header);
	xfer[1].len = buffer_size;
 	xfer[2].len = sizeof(footer);;

	return true;
}

void cleanup() {
}

int main(int argc, char** argv) {
	
	if (!init()) {
		return 1;
	}
	bool ok = receiver(); // will only return on error, just prefer it this way
	cleanup();
	if (ok) return 0;
	else return 1;
}

