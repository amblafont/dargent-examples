This document lists some challenges that show up when writing a CAN driver in Cogent using
dargent and native arrays. This shall be completed as I progress in the implementation.

The reason for focusing on the CAN driver is the recent exhuming of an old writeup 
motivating dargent based on this example.

The driver supposedly manages a MCP2515 device, whose specification can be found at https://ww1.microchip.com/downloads/en/DeviceDoc/MCP2515-Stand-Alone-CAN-Controller-with-SPI-20001801J.pdf.

# C implementation

I tried to find the original source on which the above mentionned write-up 
was based.  I looked for the mentioned function `txb_status` on github.
I found two main matching repositories:

1. https://github.com/loonwerks/formal-methods-workbench

2. https://github.com/GaloisInc/tower-camkes-odroid

The second one mentions sel4 on its front page. As we love sel4, the discussion will based on
the implementation found in its subdirectory
[data/can/components/can/](https://github.com/GaloisInc/tower-camkes-odroid/blob/master/data/can/components/can)

UPDATE 02/03/2021 Oliver Scott pointed me to this implementation:
https://github.com/seL4/camkes-vm-examples/tree/master/apps/Arm/odroid_vm/components/can/src

# Structure of the driver

## Layered architecture
The old writeup focuses on some functions in the 
[controller](https://github.com/GaloisInc/tower-camkes-odroid/blob/master/data/can/components/can/src/controller.c) file.
Some involved C types are defined in the interface file
 [data/can/components/can/include/can_inf.h](https://github.com/GaloisInc/tower-camkes-odroid/blob/master/data/can/components/can/include/can_inf.h)

Another [C interface file](https://github.com/GaloisInc/tower-camkes-odroid/blob/master/data/can/components/can/include/mcp2515.h) exhibits a block of "SPI command functions" prefixed with `mcp2515_`, all implemented in
[spi_cmd.c](https://github.com/GaloisInc/tower-camkes-odroid/blob/master/data/can/components/can/src/spi_cmd.c),
 or a block of "MCP2515 functions", typically implemented in the controller file. My guess is that the former blcok is the low-level part of the driver.  
For example, the MCP2515 function
[`txb_status`](https://github.com/GaloisInc/tower-camkes-odroid/blob/master/data/can/components/can/src/controller.c#L500) calls [`mcp2515_read_reg`](https://github.com/GaloisInc/tower-camkes-odroid/blob/master/data/can/components/can/src/spi_cmd.c#L47)
- [data/can/components/can/include/can_inf.h](https://github.com/GaloisInc/tower-camkes-odroid/blob/master/data/can/components/can/include/can_inf.h).
Interestingly, this last function eventually relies on the SPI driver 
(through the chain of calls
[`mcp2515_read_reg`](https://github.com/GaloisInc/tower-camkes-odroid/blob/master/data/can/components/can/src/spi_cmd.c#L47)
→
[`spi_transfer`](https://github.com/GaloisInc/tower-camkes-odroid/blob/master/can/components/spi/src/spi.c#L164)
→ [`do_spi_transfer`](https://github.com/GaloisInc/tower-camkes-odroid/blob/master/can/components/spi/src/spi.c#L140)
→ [`spi_xfer`](https://github.com/seL4/util_libs/blob/835e96ac320469ddc72bab66c2f64199c993233f/libplatsupport/src/plat/tk1/spi.c#L251)).

If we were to simulate the function pointer (which AutoCorres cannot deal with) that `spi_xfer` takes as an argument using a dispatch trick, then this CAN component must be compiled at the same time as the sel4 SPI driver.



**Question**: are the SPI command functions mentioned above thought to be used by
any "user", or can they be hidden? If they can be hidden, then it means that they could be
written completely in cogent without anyone noticing.

## Implemented Layer

We now have multiple choices when it comes to implement part of the CAN driver in cogent:

1. following the old write-up, we can focus on the high-level controller layer, assuming the lower layers are already implemented as they are in C;
2. same, but we could also assume that the lower-level layers are implemented in a cogent-friendly manner (if not completely in cogent);
3. Finally, we could try implementing the lower layers first (thus begging the question: can we use Louis'
cogent implementation of the SPI driver?).

In the following sections, I focus on the first route, the main reason being that I wrote them before becoming 
aware of this layered architecture.


# Layouts

The old write-up proposed a layout for the CAN frame structure.
We explain below why we consider it more relevant to design a layout for the MCP2515 registers.
The following arguments should be assessed by a system programmer.

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

## 1. Fixed-sized integers

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
getting and setting such a field would yield the set value, whereas the corresponding C behaviour
would yield the truncated set value.

## 2. Unboxed layouts

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

Another possibility consists in defining the buffer globally, and using it
somehow as a boxed data on the cogent side (by taking its address).
This global variable solution may clash if concurrent calls are performed 
(however, is this really possible?
This should be discussed with system programmers).

### Cogent feature request

Implement dargent for unboxed records.
One difficulty is that AutoCorres can't deal with taking the adress of a stack variable,
so the generated setters and getters would require to copy the whole record at each call, which
is highly inefficient. Can this be solved by declaring such functions as inline?


## 3. Copying an array

The C implementation of the above mentioned function `load_txb` copies the payload of 
the given CAN frame in the above mentionned buffer `buf` using `memcpy`:
```C
       /* Copy payload */
	memcpy(buf + DAT, frame->data, frame->dlc);
```

However, AutoCorres cannot deal with turning a stack array into a pointer.

### Workaround

The previous workarounds apply as well: allocating the buffer on the heap,
or turning it into a global variable make this possible.


A final possibility would be to implement this copy as a for loop, although
memcpy is reputed to be more efficient.

### Cogent feature request

Although this would not solve the raised issue, such copy instruction from one array to another could be made
primitive in cogent.


