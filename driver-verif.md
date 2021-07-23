This document presents general considerations about verifying a driver with
cogent.

# An example: a timer driver (for Sel4)

See https://github.com/amblafont/timer-driver-cogent.

Other examples that might be worth investigating:
- https://github.com/seL4/util_libs/blob/b0a3a4b292e3eaedfcd5770fc647768c49b3e653/libplatsupport/src/plat/hifive/pwm.c 
(but it involves U4 bitfield, see `PWMSCALE_MASK`)
- https://github.com/seL4/util_libs/blob/b0a3a4b292e3eaedfcd5770fc647768c49b3e653/libplatsupport/src/plat/bcm2837/spt.c (however the init function might be tricky)

# Communicating with a device
Depending on the device, the driver communicates with it either by sending and receiving 
data through ports or by manipulating specific memory locations.

## Communicating via ports
This method involves sending and receiving messages using output and input 
functions provided by the kernel. It has some difficulties when it comes
to verify a driver using cogent.

1. it systematically involves abstract functions: the input and output functions
provided by the kernel. Verifying cogent code involving abstract functions is
not (yet) easy. On the positive side, an adequate handling of these abstract functions
for one example could be easily reused for another example.

2. these C abstract functions are effectful: sending a message does change the
device state but the send function returns unit (more or less). 

Because of this last issue, I doubt it is ever possible to verify a driver that
communicates with ports, using cogent. In a later section, I propose some
ideas on how to extend cogent.

## Communicating via memory
This method typically involves volatile variables, because the involved
specific memory locations may not behave as regular memory. In particular, reading
the same location twice in a row may not yield the same value. 
This is problematic as it is not compatible with AutoCorres and cogent (update semantics)
memory model. Note, however, that if the driver is only writing and never reading
(such as a led driver), this may not be a problem.

One possible solution consists in manipulating the volatile memory locations using
abstract functions and give them a relevant semantics. However, I think it has
some limitations, as I am arguing in a later section.

# A challenge: nondeterministic abstract functions

## Overview of the verification story
Cogent update and value semantics straightforwardly account for nondeterministic
behaviours:
1. the semantic is inductively defined as a relation between terms and values,
rather than a function from terms to values;
2. the required semantics for abstract functions are explicitly allowed to be nondeterministic.

Of course, if the cogent program does not involve abstract functions (or at least,
no nondeterministic abstract functions), then the value and update semantics are 
actually deterministic.
Implicitly relying on this assumption, the compiler systematically generates a 
deterministic shallow embedding and a proof of correspondence with the value semantics,
letting the user fill the holes when abstract functions are involved.
It could be extended to also generate
an nondeterministic shallow embedding, which would be more suitable in case we
want to consider nondeterministic abstract functions. Since the compiler does
not currently support this, this nondeterministic shallow embedding must be manually
written, together with the proof of correspondence with the value
semantics.

A drawback of an nondeterministic shallow embedding is that it is more 
complex, since it results in a monadic program rather than purely 
functional one. However, it is still simpler than the AutoCorres embedding.
For example, it only involves the nondeterministic monad and the code is also simpler:
no guard, and isabelle sum types are directly available.

TODO: write something about the way the Bilby proof manages non determinacy

# A challenge: stateful computations, beyond indeterminacy

Suppose I want to model an abstract function `f` that returns
- a random number on the first call, 
- the same number on the second call,
- a random number on the third call,
- the same number on the fourth call
and so on.

Some far-fetched examples:
- `f` accesses a (volatile) register of some strange device
- `f` receives data using ports from some strange device.

The nondeterministic monad is not sufficient in this case for the shallow embedding:
some state must be passed around to remember the last number on an odd call.
In the far-fetched examples above, this could correspond to the device state. 
Note that we actually may want to account for this device state explicitly somehow, 
when it comes to verify the driver. But if the cogent type of `f`  is `() -> U8`,
where is the device state?

Writing a relevant shallow embedding is still possible with the right stateful monad,
but the issue is that it will no longer be possible to prove correspondence with
the value semantics. Indeed, the value semantics only support indeterminacy, and
nothing beyond: there is currently no way to give appropriate value semantics for
`f`. Maybe, value and update semantics should be extended to support stateful
semantics as well? But actually, the problem exists already at the AutoCorres level.
Indeed, to get a full chain of refinement proofs, from AutoCorres to the shallow 
embedding, abstract functions must be given semantics at each level (AutoCorres,
update and value semantics, and shallow embedding).

How do we give `f` an AutoCorres semantics? For this, we could rely on an undocumented
feature of the CParser and AutoCorres that allow to extend the standard AutoCorres state
(consisting of heaps) with a *phantom* state, in which we could put the last value returned by `f`. 

Once the AutoCorres level is settled, the value and update semantics would still
need to be extended to account for stateful computations, as argued above, together with their
proofs of correspondence. The generation of the shallow embedding could be adapted
to take into account these stateful computations, but it would be nice to still 
be able to generated a simple purely functional shallow embedding whenever it
is possible.
    
