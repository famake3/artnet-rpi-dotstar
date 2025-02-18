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
#include <sys/time.h>
#include <linux/spi/spidev.h>
#include <string.h>
#include <arpa/inet.h>
#include <sys/socket.h>
#include <errno.h>


// Configuring the Art-Net universes. Art-Net has a hierarchical 
// address space. The lowest level is the channel, representing for
// us a colour channel of a pixel. 512 channels are adressable in 
// each universe (corresponding to DMX, which also has 512 channels).
// 32768 universes are supported. We only use 510 channels per universe,
// as this corresponds to the largest number of complete RGB LEDs 
// possible (170). If the global dimmer is enabled, there is four channels
// per pixel, the number of pixels per universe is 128, and we use all
// 512 channels.


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
int NUM_PIXELS = 0;
int START_UNIVERSE = 0;
int dimmer_mode = 0;
int output_bytes_per_universe = 0;
int pixels_per_universe = 0;
int artnet_used_bytes_per_universe = 0;

#define ARTNET_MAX_BYTES_PER_UNIVERSE 512



#define DEBUG 0
#define DBG(msg) if(DEBUG) printf("[%03d] %s\n", (int)(clock() % 1000), msg); 


// Precompute some useful constants based on the settings
int num_universes;
int num_complete_universes;
int last_universe;
int pixels_in_last_universe;

//const uint32_t bitrate = 32000000; // bps
uint32_t bitrate = 8000000; // bps

uint8_t* output_buffer;
uint32_t* arrival_time; // using a cheeky 32 bit int for time
uint32_t last_frame_time = 0xFFFFFF;
uint32_t last_frame_output = 0;
int* arrival_flag;
struct timeval ts;

int startup = 3;

int fd;

// SPI transfer operation setup.  These are used w/hardware SP.
//static uint8_t header[] = { 0x00, 0x00, 0x00, 0x00 },
//               footer[] = { 0xFF, 0xFF, 0xFF, 0xFF };
static struct spi_ioc_transfer xfer[3];

uint32_t get_frame_time(uint32_t now) {
	uint32_t max = 0;
	int i;
	for (i=0; i<num_universes; ++i) {
		uint32_t cand = now - arrival_time[i];
		if (cand > max)
			max = cand;
	}
	return max;
}

void mark_frame_sent(uint32_t frame_time) {
	int i;
	for (i=0; i<num_universes; ++i) {
		arrival_flag[i] = 0;
	}
	last_frame_time = frame_time;
}

int do_output() {
	// All that spi_ioc_transfer struct stuff earlier in
	// the code is so we can use this single ioctl to concat
	// the header/data/footer into one operation:
	if (ioctl(fd, SPI_IOC_MESSAGE(3), xfer) < 0) {
		perror("sending data");
	}
}

void check_do_led_output(int universe) {
	int i_universe = universe - START_UNIVERSE;
	gettimeofday(&ts, NULL);
	uint32_t time = (uint32_t)(ts.tv_sec*1000000 + ts.tv_usec);
	arrival_flag[i_universe] = 1;
	arrival_time[i_universe] = time;

	int all_arrived = arrival_flag[0];
	int i;
	for (i=1; all_arrived && i<num_universes; ++i)
		all_arrived = arrival_flag[i];

	uint32_t frame_time = get_frame_time(time);

	if (all_arrived) { // All universes arrived!
		DBG("All have arrived, sending");
		if (frame_time < last_frame_time * 3 ||
			(time - last_frame_output) > (last_frame_time * 10)) {
			do_output();
		}
		else {
			DBG("Nope, timeout.");
		}
		last_frame_output = time;
		mark_frame_sent(frame_time);
	}
	else {
		if (frame_time * 3 < last_frame_time) {
			DBG("Sending the packet even though not all arrived!");
			do_output();
			last_frame_output = time;
			mark_frame_sent(frame_time);
		}
	}
}

// Process a packet. Returns true in most cases, false on fatal errors.
int process_packet(int packet_length, const uint8_t* buffer) {
	
	if (packet_length <= 18) {
		DBG("Too small packet");
		return 1;
	}
	uint16_t universe = *(const uint16_t*)(buffer + 14);
	//uint16_t length = *(uint16_t*)(buffer + 16);
	uint16_t length = buffer[17] | (((uint16_t)buffer[16]) << 8);

	// Skip packet if things don't add up
	if (universe < START_UNIVERSE || universe > last_universe) {
		DBG("Not our universe received");
		printf("received %d, start universe %d, last universe %d\n", 
			universe, START_UNIVERSE, last_universe);
		return 1;
	}
	if (universe == last_universe) {
		if (length > artnet_used_bytes_per_universe) {
			DBG("Invalid number of pixels received");
			printf("Got %d data\n", length);
			return 1;
		}
		length = pixels_in_last_universe*3;
	}
	else {
		if (length != artnet_used_bytes_per_universe) {
			DBG("Invalid number of pixels received");
			return 1;
		}
	}

	if (packet_length < length + 18) {
		DBG("Actual packet length shorter than specified length");
	}

	DBG("Received a valid packet!");
	// Accept it without checking more headers
	//
	int output_index = (universe-START_UNIVERSE) * output_bytes_per_universe;
	int input_index = 18;
	int i;
	int input_step = 3 + dimmer_mode;

	for (i=0; i<length; i+=3, input_index+=input_step, output_index+=4) {
		if (dimmer_mode) {
			output_buffer[output_index] = buffer[input_index] | 0xE0; // Header all 1s, 5 bits of dimmer
		}
		output_buffer[output_index+1] = buffer[input_index+2+dimmer_mode]; // B <- B
		output_buffer[output_index+2] = buffer[input_index+1+dimmer_mode]; // G <- G
		output_buffer[output_index+3] = buffer[input_index+dimmer_mode];   // R <- R
	}

	// Send to LED strip now if required
	check_do_led_output(universe);
	return 1;
}


int receiver(long refresh_milliseconds) {
  int s;
	if ((s = socket(AF_INET, SOCK_DGRAM, IPPROTO_UDP)) == -1) {
    perror("socket");
		return 0;
	}

	struct timeval tv;
	tv.tv_sec = refresh_milliseconds / 1000;
	tv.tv_usec = (refresh_milliseconds % 1000) * 1000;
	setsockopt(s, SOL_SOCKET, SO_RCVTIMEO, (char*)&tv, sizeof(struct timeval));

	struct sockaddr_in si_me;
	memset((char *) &si_me, 0, sizeof(si_me));
	si_me.sin_family = AF_INET;
	si_me.sin_port = htons(ARTNET_PORT);
	si_me.sin_addr.s_addr = htonl(INADDR_ANY);
     
	if (bind(s, (struct sockaddr*)&si_me, sizeof(si_me)) == -1) {
		return 0;
	}

	
	uint8_t buffer[1024];
	ssize_t len;
	while(1) {
		if ((len = recv(s, buffer, sizeof(buffer), 0)) == -1) {
			if (errno == EAGAIN || errno == EWOULDBLOCK) {
				do_output();
			}
			else {
				return 0;
			}
		}
		
			if (!process_packet(len, buffer)) 
				return 0;
	}
  
}


int init() {
	int i;
	
	last_universe = START_UNIVERSE + num_universes - 1;
	pixels_in_last_universe = NUM_PIXELS - (num_universes-1) * pixels_per_universe;

	// Initialize buffers and data structures
	arrival_time = (uint32_t*)malloc(num_universes * sizeof(uint32_t));
	arrival_flag = (int*)malloc(num_universes * sizeof(int));

	// Set up SPI
	if((fd = open("/dev/spidev0.0", O_RDWR)) < 0) {
		printf("Can't open /dev/spidev0.0 (try 'sudo')\n");
		return 0;
	}
	// Mode=0 and no chipselect copied from Adafruit's code
	uint8_t mode = SPI_MODE_0 | SPI_NO_CS;
	
	if (ioctl(fd, SPI_IOC_WR_MODE, &mode) < 0)
		printf("Looks like the SPI_IOC_WR_MODE ioctl failed!\n");

	// Speed!
	int err;
	if ((err = ioctl(fd, SPI_IOC_WR_MAX_SPEED_HZ, &bitrate)) < 0) {
		printf("Looks like the SPI_IOC_WR_MAX_SPEED_HZ ioctl failed: %d!\n", err);
		perror("ioctl");
	}
	uint8_t bpw = 8;
	if ((err = ioctl(fd, SPI_IOC_WR_BITS_PER_WORD, &bpw)) < 0) {
		printf("Looks like the SPI_IOC_WR_BITS_PER_WORD  ioctl failed: %d!\n", err);
		perror("ioctl");
	}

	// Set up buffer
	const int buffer_size = NUM_PIXELS*4;
	output_buffer = (uint8_t*)malloc(buffer_size);
	if (output_buffer == NULL) {
		printf("Unable to allocate buffer (not enough memory?)\n");
		return 0;
	}
	// Initialize to black (leading byte must always be 0xFF, three next
	// bytes are the rgb components
	for (i=0; i<buffer_size; i+=4) {
		output_buffer[i] = 0xFF;
		output_buffer[i+1] = 0;
		output_buffer[i+2] = 0;
		output_buffer[i+3] = 0;
	}

	// For the footer we should send one FF byte for every 16 pixels
	// (rounded up). It's not important what we send, but it's good to not send
	// zeros, as that might be interpreted as a header.
	const int footer_size = (NUM_PIXELS + 15) / 16;
	uint8_t* footer = (uint8_t*)malloc(footer_size);
	if (footer == NULL) {
		printf("Unable to allocate footer buffer (not enough memory?)\n");
		return 0;
	}
	for (i=0; i<footer_size; ++i) {
		footer[i] = 0xFF;
	}

	// Set up SPI output data structures
	memset((char*) xfer, 0, sizeof(xfer));
	xfer[0].tx_buf = 0;
	xfer[1].tx_buf = (unsigned long)output_buffer;
	xfer[2].tx_buf = (unsigned long)footer;
	xfer[0].len = 4;
	xfer[1].len = buffer_size;
 	xfer[2].len = footer_size;

	return 1;
}

void cleanup() {
}

int main(int argc, char** argv) {

	int refresh_interval = 0;
	if (argc == 4 || argc == 5) {
		dimmer_mode = atoi(argv[1]);
		START_UNIVERSE = atoi(argv[2]);
		NUM_PIXELS = atoi(argv[3]);
		if (argc == 5) {
			refresh_interval = atoi(argv[4]);
		}
		if (dimmer_mode != 0 && dimmer_mode != 1) {
			printf("ERROR: Dimmer mode should be 0 or 1.");
			return 1;
		}
	}
	else {
		printf("use: %s FIRST_UNIVERSE NUM_PIXELS [REFRESH_INTERVAL]\n", argv[0]);
		printf("     DIMMER_MODE:      Set to 1 if using four channnels per pixel, where\n");
		printf("                       the first channel is a global (hardware) dimmer. The\n");
		printf("                       dimmer supports 5 bits dynamic range, and may use slow PWM.\n");
		printf("                       Set to 0, use 3 channels per pixel and set dimmer to\n");
		printf("                       full brightness.\n");
		printf("     FIRST_UNIVERSE:   Hardware-ID (zero based) of first DMX universe\n");
		printf("     NUM_PIXELS:       Number of pixels to drive. If larger than 170,\n");
		printf("                       multiple sequentially numbered universes will be\n");
		printf("                       used.\n");
		printf("     REFRESH_INTERVAL: If specified, pixels are refreshed with buffered\n");
		printf("                       values every REFRESH_INTERVAL milliseconds, even\n");
		printf("                       if no data is received.\n");
		exit(1);
	}
	
	pixels_per_universe = ARTNET_MAX_BYTES_PER_UNIVERSE / (3 + dimmer_mode);
	// Round up universe count
	num_universes = (NUM_PIXELS + pixels_per_universe + 1) / pixels_per_universe;
	num_complete_universes = NUM_PIXELS / pixels_per_universe;
	artnet_used_bytes_per_universe = pixels_per_universe * (3 + dimmer_mode);

	// Output always includes the dimmer/header byte regardless of whether they
	// are used, and includes 3 bytes of colour data.
	output_bytes_per_universe = pixels_per_universe * 4;
	
	if (!init()) {
		return 1;
	}

	int ok = receiver(refresh_interval); // will only return on error, just prefer it this way
	cleanup();
	if (ok) return 0;
	else return 1;
}

