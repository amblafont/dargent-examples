
In this file, I explore the theoretical possibility of compiling dargent to 
cogent directly.

Source language
: Cogent with layout indications

Target language
: Cogent with
- arrays
- FFI casts `U32 → B` and `B → U32`, for any boxed record `B`.

Extending the cogent language with casts is an option that looks tedious.
Another possibility is to implement these casts as FFI: this is the option that
I consider here.

It should be possible to ignore the need for arrays (replacing them with 
records with as many U32 fields as the size of the array)
in the first place.

# Comparison with the current adopted approach

The current adopted approach consists in compiling directly to C.
The only step currently missing in our current approach is the 
correspondence proof between the update semantics and the monadic code, more
precisely proofs about custom getters and setters.

The advantage of the current approach is that not much work is required
at the level of the cogent compiler, whereas what I propose here would involve
an extra compilation phase (targeting cogent). Also, the verification framework 
has already been adapted to the current adopted approach.

The motivation for this proposal is the hope that get/set lemmas are easier to 
prove at the level of the update semantics. 

Recall that there are 4 types of get/set lemmas:

1. `val_rel x v ⇒ val_rel x (get_a (set_a p v))` 
2. `get_a ∘ set_b = get_a`
3. `C_get = direct_get`
4. `C_set = direct_set`

The current proposal would help for the last two lemmas, but so far I have not 
yet been confronted to difficult instances of them.

The first two lemmas are refering to direct isabelle definitions of 
getters/setters, so they do not depend on whether we are compiling to C or to
cogent. I have been confronted to difficult instances of them, and I am getting 
help from Vincent.

All in all, considering the point we reached in the current adopted approach,
the benefits of this dargent-to-cogent compilation are not obvious, but still
I think it is worth thinking of this possibility.

# The need for casts

Consider the following simple dargent specification:

`
type A = { a : B }  layout record { a : pointer at 0B }
`

where `B` is a boxed record type. The C custom getter `get_a` returns a value
of type `⟦ B ⟧`, where `⟦ B ⟧` denotes the compilation of the cogent type
`B` (note that it does not depend on the layout indications).
Roughly, the code for `get_a` is:

`
⟦ B ⟧ * get_a (U32[1] array) {
   return (⟦ B ⟧ *) array[0];
}
`

If we were to compile this getter to cogent rather to C, we thus need a cast
 from U32 to `B` (in the C code, this is `⟦ B ⟧ *`). 

The setter involves the converse cast from `B` to U32.

I have checked on a simple example (see 
[here](bucket/nested_boxed.cogent)) 
that AutoCorres is fine with the generated C casts: I have been able to prove the
correspondence statement between the monadic embedding and the update semantics.

# Breaking linearity with casts

The existence of casts `U32 → B` and `B → U32` would provide a trick to get
around the linearity constraints on `B`, as `U32` is not linear.
One workaround would be to introduce an abstract linear type `Ptr` in cogent.

However, 

- we should not enforce that all the elements of the array representing a record 
(according to its custom layout) are of type `Ptr`, because this record may 
contain unboxed non-linear fields (such as `U32` fields);

- I have been told that system people already avoid the linearity constraints
by using FFI calls, so the trick already exists somehow;

- introducing this new type involves additionnal work;

- we could hide these cast operations to the programmer (this may be in fact
necessary as I don't know how to give proper value semantics to casts, see 
the later section about this).

For these reasons, I propose to ignore this issue.

# Verification pipeline for dargent

I suggest the following verification process for a dargent program:
1. Correspondence proof between the value and update semantics
2. Compilation to cogent with arrays and FFI casts
3. Monadic to update semantics correspondence proof for the ouput program
4. Correspondence proof between the update semantics of the dargent program
and the compiled cogent program.

Steps 1 and 3 are already addressed by the current verification framework.

An alternative possibility would be to prove correspondence between the value 
semantics of the input program and the output cogent program. Unfortunately,
as explained below, I don't know how to provide casts with value semantics.



# Update/Value semantics for casts

We must provide update and value semantics for casts. Note that the
formalization differs from the paper: the formalization defines
the semantics of abstract functions as relations between input and output,
whereas in the paper the semantics consists in functions from input to output.
The formalization thus allows partially defined abstract functions.

## Update semantics

In the formalization of the update semantics, there is a value constructor for 
pointers `UPtr "'l" repr`. We assume now that `'l = U32`.
Hopefully, this is a specialization that does not break the formalization
pipeline.

It is straightforward to define the update semantics for a FFI cast `U32 → B`.
More formally, `⟦cast⟧ᵤ(n, μ) = (UPtr n B, μ)`, where `μ` is a heap
(partially mapping pointers to values).

## Value semantics

The value semantics is not obvious to specify. It seems to require some 
 heap environment in the value semantics, but we don't want that at
 this level of abstraction.

<!-- and the modified heap. Casts do not modify the heaps. Consider the example of  -->
<!-- a cast `U32 → B`. We would enforce, for example, -->
<!--  `cast(52) = p`, where `p` is a pointer to a value -->
<!-- `b` of type `B` (according to input heap), corresponding to a value  -->
<!-- `b'` (in the value semantics). -->
<!-- More formally, `⟦cast⟧ᵤ(52, μ) = (p, μ)` if `μ(p) = b`. -->
<!-- In the value semantics, we would enforce `⟦ cast ⟧ᵥ (52) = b'`. -->

<!-- # FFI requirements for casts -->

<!-- If these casts are FFI, do they satisfy the FFI requirements described in  -->
<!-- section 3.3.2 of the ICFP'16 paper? -->


 
<!-- As argued above, casts do not modify heaps (they do not create new pointers that -->
<!-- did not exist before). Furthermore, they do not introduce new readable or  -->
<!-- writable pointers. Therefore, it is easy to check that they satisfy the FFI -->
<!-- requirements. -->

<!-- # Value ⇒ Update refinement with casts -->

<!-- Following what we previously said about FFI requirements, in fact we have a  -->
<!-- scheme of refinement proofs, parameterized by pointers `p`, and associated -->
<!-- values `b` and `b'`. -->







