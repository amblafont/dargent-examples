We investigate reimplementing part of the [LibOpenCM3 library](http://libopencm3.org/) 
with cogent + dargent.

This library was found by searching 'arm' on github: indeed, arm devices typically
rely on MMIO communication rather than ports, which are currently not suitable
for verification (See [detailed explanations](../driver-verif.md)).

Some examples
  * https://github.com/libopencm3/libopencm3/tree/master/lib/stm32/common/opamp_common_v1.c (not very interesting, but definitely a use case for dargent)
  * https://github.com/libopencm3/libopencm3/tree/master/lib/swm050/timer.c
  * https://github.com/libopencm3/libopencm3/tree/master/lib/pac55xx/can.c (a CAN driver)
  * https://github.com/libopencm3/libopencm3/tree/master/lib/msp432/e4/gpio.c (there is a fixed size for loop that could be unfolded to avoid abstract functions)


