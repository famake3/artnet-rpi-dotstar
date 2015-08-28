/*------------------------------------------------------------------------
 *
 *  Famake's Art-Net -> DotStar SPI proxy
 *
 *
 * Based on Adafruit DotStar Raspberry Pi lib 
 * (https://github.com/adafruit/Adafruit_DotStar_Pi)
 *
 * Art-Net interface for the DotStar LED strips. Supports a minimal 
 * subset of the Art-Net protocol, needed to push pixels to the strips.
 * The rationale for choosing Art-Net is that it is already a (de facto)
 * standard for lighting control, and the LED strips become available to
 * applications such as Madrix.
 *
 * This code ditches the Python interface and works with C only, it also
 * does not support bit-banging.
 *
 * 	-- Functional overview --
 * 
 * 	The program uses two threads:
 *
 *      o Network receiver thread
 *      o SPI sender thread
 *
 *
 * The code is licensed under the GNU Lesser General Public License.
 * See the Adafruit library for details.
 *------------------------------------------------------------------------*/

#include <fcntl.h>
#include <sys/mman.h>
#include <sys/ioctl.h>
#include <pthread.h>
#include <linux/spi/spidev.h>

#define SPI_MOSI_PIN 10
#define SPI_CLK_PIN  1

#define ARTNET_BYTES_PER_UNIVERSE 510
#define OUTPUT_BYTES_PER_UNIVERSE 510*4/3

// Configuring the Art-Net universes. Art-Net has a hierarchical 
// address space. The lowest level is the channel, representing for
// us a colour channel of a pixel. 512 channels are adressable in 
// each universe (corresponding to DMX, which also has 512 channels).
// 32768 universes are supported. We only use 510 channels per universe,
// as this corresponds to the largest number of complete RGB LEDs 
// possible (170).
//
// This program buffers data coming in via UDP until it has loaded a full
// frame, then sends it (to be determined)
// Some logic is required to maintain synchronization with the network
// input.
//
const uint8_t universe_ids[] = {1, 2, 3};
const uint8_t num_universes = sizeof(universe_ids) / sizeof(const uint8_t);
const uint8_t universe_data[num_universes * ARTNET_BYTES_PER_UNIVERSE];

const uint32_t bitrate = 8000000;

uint8_t* output_buffer;

int fd;

// SPI transfer operation setup.  These are used w/hardware SP.
static uint8_t header[] = { 0x00, 0x00, 0x00, 0x00 },
               footer[] = { 0xFF, 0xFF, 0xFF, 0xFF };
static struct spi_ioc_transfer xfer[3] = {
 { .rx_buf        = 0,
   .len           = sizeof(header),
   .delay_usecs   = 0,
   .bits_per_word = 8,
   .cs_change     = 0 },
 { .rx_buf        = 0,
   .delay_usecs   = 0,
   .bits_per_word = 8,
   .cs_change     = 0 },
 { .rx_buf        = 0,
   .len           = sizeof(footer),
   .delay_usecs   = 0,
   .bits_per_word = 8,
   .cs_change     = 0 }
};

// Initialize DotStar object
static int DotStar_init(DotStarObject *self, PyObject *arg) {
	uint8_t *ptr;
	uint32_t i;
	// Set first byte of each 4-byte pixel to 0xFF, rest to 0x00 (off)
	for(ptr = self->pixels, i=0; i<self->numLEDs; i++) {
		*ptr++ = 0xFF; *ptr++ = 0x00; *ptr++ = 0x00; *ptr++ = 0x00;
	}
	return 0;
}



// Set strip data to 'off' (just clears buffer, does not write to strip)
static PyObject *clear(DotStarObject *self) {
	uint8_t *ptr;
	uint32_t i;
	for(ptr = self->pixels, i=0; i<self->numLEDs; i++, ptr += 4) {
		ptr[1] = 0x00; ptr[2] = 0x00; ptr[3] = 0x00;
	}
	Py_INCREF(Py_None);
	return Py_None;
}

// Valid syntaxes:
// x.setPixelColor(index, red, green, blue)
// x.setPixelColor(index, 0x00RRGGBB)
static PyObject *setPixelColor(DotStarObject *self, PyObject *arg) {
	uint32_t i, v;
	uint8_t  r, g, b;

	switch(PyTuple_Size(arg)) {
	   case 4: // Index, r, g, b
		if(!PyArg_ParseTuple(arg, "Ibbb", &i, &r, &g, &b))
			return NULL;
		break;
	   case 2: // Index, value
		if(!PyArg_ParseTuple(arg, "II", &i, &v))
			return NULL;
		r = v >> 16;
		g = v >>  8;
		b = v;
		break;
	   default:
		return NULL;
	}

	if(i < self->numLEDs) {
		uint8_t *ptr = &self->pixels[i * 4 + 1];
		*ptr++ = b; // Data internally is stored
		*ptr++ = g; // in BGR order; it's what
		*ptr++ = r; // the strip expects.
	}

	Py_INCREF(Py_None);
	return Py_None;
}

// Write data in the format used by Dotstar, each pixel gets four bytes, 
// first is 0xFF, the others are the colour in BGR order
static void raw_write(DotStarObject *self, uint8_t *ptr, uint32_t len) {
	if(self->fd >= 0) { // Hardware SPI
		xfer[1].tx_buf = (unsigned long)ptr;
		xfer[1].len    = len;
		// All that spi_ioc_transfer struct stuff earlier in
		// the code is so we can use this single ioctl to concat
		// the header/data/footer into one operation:
		(void)ioctl(self->fd, SPI_IOC_MESSAGE(3), xfer);
	}
}

// Issue data to strip.  Optional arg = raw bytearray to issue to strip
// (else object's pixel buffer is used).  If passing raw data, it must
// be in strip-ready format (4 bytes/pixel, 0xFF/B/G/R) and no brightness
// scaling is performed...it's all about speed (for POV & stuff).
static PyObject *show(DotStarObject *self, PyObject *arg) {
	if(PyTuple_Size(arg) == 1) { // Raw bytearray passed
		Py_buffer buf;
		if(!PyArg_ParseTuple(arg, "s*", &buf)) return NULL;
		raw_write(self, buf.buf, buf.len);
		PyBuffer_Release(&buf);
	} else { // Write object's pixel buffer
		if(self->brightness == 0) { // Send raw (no scaling)
			raw_write(self, self->pixels, self->numLEDs * 4);
		} else { // Adjust brightness during write
			uint32_t i;
			uint8_t *ptr   = self->pixels;
			uint16_t scale = self->brightness;
			if(self->fd >= 0) { // Hardware SPI
				// Allocate pBuf if using hardware
				// SPI and not previously alloc'd
				if((self->pBuf == NULL) && ((self->pBuf =
				  (uint8_t *)malloc(self->numLEDs * 4)))) {
					memset(self->pBuf, 0xFF,
					  self->numLEDs * 4); // Init MSBs
				}

				// Scale from 'pixels' buffer into
				// 'pBuf' (if available) and then
				// use a single efficient write
				// operation (thx Eric Bayer).
				uint8_t *pb = self->pBuf;
				for(i=0; i<self->numLEDs;
				  i++, ptr += 4, pb += 4) {
					pb[1] = (ptr[1] * scale) >> 8;
					pb[2] = (ptr[2] * scale) >> 8;
					pb[3] = (ptr[3] * scale) >> 8;
				}
				raw_write(self, self->pBuf,
				  self->numLEDs * 4);
			} 
		}
	}

	Py_INCREF(Py_None);
	return Py_None;
}

// Given separate R, G, B, return a packed 32-bit color.
// Meh, mostly here for parity w/Arduino library.
static PyObject *Color(DotStarObject *self, PyObject *arg) {
	uint8_t   r, g, b;
	PyObject *result;

	if(!PyArg_ParseTuple(arg, "bbb", &r, &g, &b)) return NULL;

	result = Py_BuildValue("I", (r << 16) | (g << 8) | b);
	Py_INCREF(result);
	return result;
}

// Return color of previously-set pixel (as packed 32-bit value)
static PyObject *getPixelColor(DotStarObject *self, PyObject *arg) {
	uint32_t  i;
	uint8_t   r=0, g=0, b=0;
	PyObject *result;

	if(!PyArg_ParseTuple(arg, "I", &i)) return NULL;

	if(i < self->numLEDs) {
		uint8_t *ptr = &self->pixels[i * 4 + 1];
		b = *ptr++; g = *ptr++; r = *ptr++;
	}

	result = Py_BuildValue("I", (r << 16) | (g << 8) | b);
	Py_INCREF(result);
	return result;
}

static PyObject *_close(DotStarObject *self) {
	if(self->fd) {
		close(self->fd);
		self->fd = -1;
	} else {
		INP_GPIO(self->dataPin);
		INP_GPIO(self->clockPin);
		self->dataMask  = 0;
		self->clockMask = 0;
	}
	Py_INCREF(Py_None);
	return Py_None;
}

static void DotStar_dealloc(DotStarObject *self) {
	_close(self);
	if(self->pBuf)   free(self->pBuf);
	if(self->pixels) free(self->pixels);
	self->ob_type->tp_free((PyObject *)self);
}


int spi_thread(void* arg_TODO) {
	return 0;
}

int init() {
	// Initialize buffers and data structures
	const int buffer_size = num_universes*OUTPUT_BYTES_PER_UNIVERSE;
	output_buffer = (uint8_t)malloc(buffer_size);
	if (output_buffer == NULL) {
		fprintf("Unable to allocate output buffer");
		return 0;
	}
	// Initialize leading 0xFF bytes before each pixel
	memset(output_buffer, 0xFF, buffer_size);



	// Set up SPI
	if((fd = open("/dev/spidev0.0", O_RDWR)) < 0) {
		printf("Can't open /dev/spidev0.0 (try 'sudo')\n");
		return 0;
	}
	// Mode=0 and no chipselect copied from Adafruit's code
	uint8_t mode = SPI_MODE_0 | SPI_NO_CS;
	ioctl(fd, SPI_IOC_WR_MODE, &mode);
	ioctl(self->fd, SPI_IOC_WR_MAX_SPEED_HZ, bitrate);
	xfer[0].speed_hz = xfer[1].speed_hz = xfer[2].speed_hz = self->bitrate; 
	// 
	xfer[0].tx_buf = (unsigned long)header;
	xfer[2].tx_buf = (unsigned long)footer;

	return 1;
}

int main(int argc, char** argv[]) {
	
	if (!init()) {
		exit(1);
	}
	pthread_create();
	return 0;
}

