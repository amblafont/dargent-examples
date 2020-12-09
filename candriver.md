This document lists some challenges that show up when writing a CAN driver in Cogent using
dargent and native arrays. This shall be completed as I progress in the implementation.

# C implementation

We base our discusssion on some C implementation found here

- https://github.com/smaccm/smaccm/blob/master/models/Trusted_Build_Test/can/components/can/src/controller.c
- https://github.com/smaccm/smaccm/blob/master/models/Trusted_Build_Test/can/include/can_inf.h

The driver supposedly manages a MCP2515 device, whose specification can be found at https://ww1.microchip.com/downloads/en/DeviceDoc/MCP2515-Stand-Alone-CAN-Controller-with-SPI-20001801J.pdf.



# Layouts

An older write-up motivating dargent proposed a layout for the CAN frame structure.
We explain below why we consider it more relevant to design a layout for the MCP2515 registers.
The following arguments should be checked by discussing with a system programmer.

To implement a CAN driver, the system programmer needs to check the specification of the MCP2515 device.
Then, he is free to design the interface of his choice that he wants to make available to
the user space. 
For example, a CAN driver provides a function taking a CAN frame structure as input, and update
the MCP2515 registers in order to send the frame on the network.
In the above C implementation, the CAN frame structure is user-friendly (it is a C struct), but
does not match the layout of the MCP2515 registers which are basically accounted as an array of bytes.
Thus, the C implementation needs to translate the user-friendly CAN frame structure to
the layout of the MCP2515 registers.
It seems that dargent would be useful to address this translation automatically, and to this
end the layout should be assigned to the MCP2515 register (an array of bytes) rather than
to the (user-friendly) CAN frame structure.

That said, there is still a motivation for designing a custom layout for the CAN frame structure:
to make it as compact as possible in memory (because such a driver may be used in low-memory devices). 
This is probably the reason why the CAN frame structure in the C implementation specifies the length
in bits of each field, as follows.

```C
struct can_id {
	uint32_t id:29;
	uint32_t exide:1;
	uint32_t rtr:1;
	uint32_t err:1;
};

struct can_frame {
	struct can_id ident;
	uint8_t prio:2;
	uint8_t dlc:4;
	uint8_t data[CAN_MAX_DLC] __attribute__((aligned(8)));
};
```



# Challenges

## Fixed-sized integers

Some MCPI2515 register contains a 4 bit long integer, called `dlc`
This is the length of data in the frame. 

However, Cogent only offer standard sized integers, such as U8, U16, or U32.

### Workaround

This 4 bit long integer could be represented as an array of booleans of size 4, but
then we forget that we really are interested in is the overall integer.


### Cogent feature request

Cogent could offer a new family of types `Int n` for each n < 64, together with downcasting
(by truncating).
Such types need not have primitive operations: one could always upcast them to standard
sized integers, perform the usual operations, then downcast them (this is how
it would be written in C anyway).

Alternatively, instead of adding these new types explicitely, primitive integer types could
be assigned smaller bitranges than they need. In this case, the setters and getters would perform
the required truncation or upcasting.
However, this would require to adapt the shallow embedding. Indeed, for the shallow embedding,
getting and setting such a field should retrieve the set value, whereas the corresponding C behaviour
would yield the truncated set value.

## Unboxed layouts

The C implementation of the function sending a given frame starts with allocating a 
an array of bytes on the stack, that is later copied to the MCPI2515 registers.

```C
void load_txb(int txb_idx, struct can_frame *frame)
{
	uint32_t sid, eid;
	uint8_t buf[MAX_BUF_LEN];
```

This buffer `buf` is the one for which we want a custom layout matching
the specification of the MCPI2515 registers.

### Workaround

Allocate this buffer on the heap (via an external C function).
The drawback is that allocating on the heap is costly.

An alternative workaround consists in defining the buffer globally, but this
may clash if concurrent calls are performed (however, is this really possible?
This should be discussed with system programmers).

### Cogent feature request

Implement dargent for unboxed records.
One difficulty is that AutoCorres can't deal with taking the adress of a stack variable,
so the generated setters and getters would require to copy the whole record at each call, which
is highly ineffecient. Can this be solved by declaring such functions as inline?


## Copying an array

The C implementation of the above mentioned function `load_txb` copies the payload of 
the given CAN frame in the above mentionned buffer `buf` using `memcpy`:
```C
       /* Copy payload */
	memcpy(buf + DAT, frame->data, frame->dlc);
```

However, AutoCorres cannot deal with turning a stack array into a pointer

### Workaround

The previous workarounds apply as well: allocating the buffer on the heap or turning it into
a global variable makes this possible.
An alternative possibility would be to implement this copy as a for loop, although
memcpy is reputed to be more efficient in general.


### Cogent feature request

Although this does not solve the raised issue, such copy instruction from one array to another could be made
primitive in cogent.


