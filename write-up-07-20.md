This document provides the following information:
1. An overview of dargent;
2. An overview of the verification framework;
3. How the verification framework was adapted for dargent.


# Overview of Dargent

Dargent offers the possibility to assign any (boxed) record type a custom layout describing how the data 
should be mapped into memory.
A record specified with a custom layout is compiled to a record
with a single field consisting of an array of bytes (more precisely, it is an array of words).
This array **represents** the record: it contains enough information to retrieve
the values of the fields. And indeed, when compiling a record with a custom layout, custom
field getters are generated along (in C), retrieving the required field from the 
representing array. Similarily, custom field setters are also generated.

Roughly, for a record `{ foo : A, ...}`, the custom getter for the field `foo`
takes an array of bytes as input and outputs a value of type `A`.
<!-- We informally denote its type by `get_foo : Bytes [] → A`  -->

The custom setter for the same field takes an array of bytes and a value of 
type `A`, and updates the array so that it represents the updated record.
<!-- We informally denote its type by `set_foo : Bytes [] → A → ()` -->

<!-- Custom getters and setters are generated along by the compiler (in C) for each field  -->
<!-- of the original cogent record, respecting the layout specification.  -->
<!-- They are used to compile the cogent Member/Take/Put operations. -->

## Example

Consider the cogent record:
```cogent
    type Example =
      { struct : #{a : U32, b : Bool},
        ptr    : { c : U8 },
        sum    : < A Bool | B U8 >
      }
```
<!-- To understand what a layout should specify, we need -->
<!-- In case a custom layout is provided, this record will be (roughly) compiled to  -->
<!-- an array of bytes  -->
<!-- ```C -->
<!-- typedef Example = Bytes[]; -->
<!-- ``` -->
<!-- If provide a layout, this record  -->
A layout for this record details how each field is 
represented in the array of bytes.
| Field | Type | Information encoded in the array |
| --- | --- | --- |
| `struct` | *immediate* (`#`) record | `a : U32` and `b : Bool` |
| `ptr` | *mediate* (boxed) record | pointer to a structure `{ c : U8 }` |
| `sum` | variant | the tag (`A` or `B`), the `A` and `B`-arguments |

A layout for this record would specify
1. where `a : U32` and `b : Bool` are located (in the representing array of 
bytes),
2. where the pointer to a structure`{ c : U8 }` is located,
3. what are the (integer) tag values corresponding to the constructors `A` and `B`,
4. where the tag is located,
5. where the `A`-argument of type `Bool` is located,
6. where the `B`-argument of type `U8` is located.

Only the locations of the `A` and `B` arguments can overlap. This 
is safe because at each time, only one of them is relevant, 
depending on the tag value.

## Abstract compilation of records

<!-- In this section, we provide an abstract view on the compilation of cogent  -->
<!-- records. -->

Without custom layouts, a cogent record is simply compiled to a C struct with
as many fields as the original record: if `T = { a : A, b : B}`, then
`⟦ T ⟧ = struct { a : ⟦ A ⟧, b : ⟦ B ⟧ }`, where `⟦ - ⟧` denotes the
compilation of cogent to C.
<!-- Then, the get/set operations are easily given using the usual record -->
<!-- operations in C. In practice, the get/set operations are directly inlined at -->
<!-- compilation time. -->

### Compilation to C

<!--Nothing fundamentally enforces a cogent record type to be compiled
as straightforwardly as described above. -->
The Dargent extension to the compiler relies on the fact that, as long 
as get/set operations are provided for each field, we are free to choose the compiled record 
type. An indeed, assigning a custom layout `l` to a cogent 
record `T` results in a C type `⟦ T ⟧ₗ`, consisting of a C struct with a 
 a fixed sized array of bytes  as single field.
Then, the get/set operations are generated according
to the provided layouts.

Consider, for example, a field `a : A` in `T`. The prototypes for the 
corresponding get/set operations are:
```C
⟦ A ⟧ get_a(⟦ T ⟧ₗ t) ;
void set_a(⟦ T ⟧ₗ t, ⟦ A ⟧ a) ;
```

### Overview of the required properties of get/set operations

As argued above, the compilation of a cogent record type `T` to C can be 
arbitrary as long as get/set operations are provided.
When it comes to formally verify the compiled C program, these get/set 
operations are expected to satisfy some properties:
1. setting a field does not affect the result of getting another field;
2. getting a set field should return the set value (or at least an equivalent 
value).

These properties are discussed in the later section about get/set lemmas.


<!-- Note that the layout `l` does not affect the compilation of `T`: the return type -->
<!-- of the getter  -->
<!-- not the compilation -->


<!-- Given a record type `T`, we denote by `⟦ T ⟧` its associated compiled C type. -->
<!-- When compiling cogent programs involving `T`, we don't need to know -->
<!-- what exactly `⟦ T ⟧` is: we only need getter and setter operations, for each  -->
<!-- field of the original cogent type `T`.  -->
<!-- The generation of these getters/setters -->
<!-- can be considered as a separate task. -->



<!-- Without custom layouts, a cogent record is simply compiled to a C struct with -->
<!-- as many fields as the original record: if `T = { a : A, b : B}`, then -->
<!-- `⟦ T ⟧ = struct { a : ⟦ A ⟧, b : ⟦ B ⟧ }`. -->
<!-- Then, the get/set operations are easily given using the usual record -->
<!-- operations in C. In practice, the get/set operations are directly inlined at -->
<!-- compilation time. -->

<!-- Nothing fundamentally enforces a cogent record type to be compiled -->
<!-- as straightforwardly, as long as get/set operations are provided. Dargent takes -->
<!-- advantage of this: assigning a custom layout `l` to a cogent record `T` results -->
<!-- in a different compiled C type, that we denote by -->
<!-- `⟦ T ⟧ₗ`. In general, this consists of a C struct with a single field which -->
<!-- is a fixed sized array of bytes (the size is determined by the layout). -->
<!-- Now, the get/set operations are no longer obvious and are generated according -->
<!-- to the provided layouts. -->




 
<!-- ## Packing/Unpacking -->

<!-- Importantly, `⟦T⟧`, the return type of the custom getter, -->
<!-- does not depend on the layout specification: -->
<!-- it is the C type to which `T` would be compiled to -->
<!-- if all layout specifications were removed. -->
<!-- It means that a kind of packing/unpacking is systematically -->
<!-- involved in custom getters/setters.  -->

<!-- ```cogent -->
<!--     type R1 = { f1 : .. , .. } layout .. -->
<!--     type R2 = { f2 : .. , .. } -- same record type as R1, without layout -->
    
<!--     pack_unpack : (R1, R2) -> (R1, R2) -->
<!--     pack_unpack (r1 { f1, ..}, r2 { f2, ..}) = (r1 {f1 = f2, ..}, r2 {f2 = f1, ..}) -->

 

<!-- ## Casts and AutoCorres -->
 
<!-- Custom getters involve casts from bytes to  -->
<!-- pointers (in the case the accessed field is a cogent boxed record, which  -->
<!-- corresponds to a pointer to a structure in C). AutoCorres is fine with it:  -->
<!-- I have been able to carry out the verification proof for such an example. -->

<!-- Similarily, custom setters involve casts from pointers to bytes. -->

# Structure of the verification framework

## Overview
The compilation of a cogent program generates multiple components:
1. a C program,
2. an Isabelle program (*shallow embedding*),
3. an Isabelle proof of correspondence between the C program and the Isabelle
program.

The purpose of the two last components is to provide the following indirect way 
for formally verifying the C program:
1. prove the expected properties about the Isabelle program
2. use the proof of correspondence to apply them to the C program.

The motivation for this approach is that it is simpler to reason about 
(functional) Isabelle programs than about C programs.

In the following section, we give an overview of the third component.

## Correspondence between C and Isabelle programs.

Stating the correspondence between the C and the isabelle programs requires
a representation of the C code in Isabelle.
For this, we use the AutoCorres framework.

The correspondence proof relies on
an intermediate layer between the C program and the Isabelle program.
This layer consists of a representation of the cogent program in 
Isabelle, as a term describing the cogent syntax
(*deep embedding*). Its type is a
 datatype defined in the Isabelle library that is systematically imported in 
 the generated theory files. 
Two semantics are defined for the deep embedded syntax in this library:
1. an *update semantics*, specifying the execution in a stateful environment
2. a more abstract *value semantics*, which avoids talking about pointers and 
states.

An abstract proof of correspondence between these two semantics is provided in
the library, for any cogent program (in the sense of deep embedding). 

For a particular cogent program, the compiler generates a shallow and a deep embedding,
with two proofs of correspondence:
1. one between the isabelle program (shallow embedding) and the deep embedding
  with value semantics,
2. one between the deep embedding with update semantics and the C program.

Chaining the correspondence lemmas results in a correspondence between
the C program and the Isabelle program, as desired.

<!-- - the C program and the deep embedding -->
<!-- - the deep embedding and the shallow embedding -->

<!-- 3. an abstract representation of the cogent program in Isabelle (*deep embedding*) -->
# Extending verification framework with Dargent

First, let us list some components that we don't need to adapt for Dargent:
- shallow and deep embedding;
- value and update semantics (for the deep embedding)

In fact, the main component that must be adapted is the proof of correspondence 
between the update semantics and the C code.
The crucial change is that getting or setting a field in the update semantics
does not correspond anymore to getting or setting a corresponding C field.
Indeed, at the C level, a field is now encoded in an array of bytes according to
the layout. As discussed earlier, the generated C code provides custom functions
for getting and setting a field encoded in an array. Getting or setting a field
in the update semantics correspond to a C call of such functions.

In the following subsections, we discuss what changes were necessary to take Dargent
into account:
1. adapting the record lemmas, which are elementary correspondence statements about
basic record operations (Take/Put/Member);
2. adapting the value relation;
3. generate get/set lemmas, stating some expected properties about the custom
getters and setters

## Record lemmas

Before tackling the correspondence between the deep embedded main function and 
its C compiled counterpart, the verification process starts with proving
a bunch of basic lemmas about accessing and setting records, for each possible
field operation in cogent (Take/Put/Member).
More precisely, such a *record lemma* states a correspondence between such a field operation
and its C compiled version.

The main proof tactic proving the correspondence for the deep embedded main function relies 
 on these lemmas in such a way that
extending the verification process with Dargent only requires to adapt these basic lemmas.
The ML code of the main proof tactic remains untouched.

The changes in the statements of these lemmas account for the fact that for example
a Take operation is no longer compiled to a direct field access, but to a call 
to a custom C getter.
The adapted automatic proof of these new statements relies on some additionnal get/set lemmas,
(detailed in a later section below), that ought to be proven before.

## Value relation for records with layout

### Overview of the value relation
The correspondence statement between the update semantics and the C code relies
on the definition of a value relation, for each C type, between
- a value, in the sense of the update semantics, and
- an Isabelle term whose type represents the C type.
<!-- Schematically, we denote this relation by `~ᵥ(T) : UpdateVal → T → bool`,  -->
<!-- for any involved C type `T`. -->

As mentionned above, we use AutoCorres to get a representation of the C code
in Isabelle. In particular, AutoCorres represents each C type
 directly as an Isabelle type. For example, the C type
`struct { u8 field1 ; u16 field2 }`, 
is represented by the isabelle record type
`{ field1 : u8, field2 : u16 }`, where `u8` and `u16` are defined
in the AutoCorres library.
Then, C functions are represented as *monadic* Isabelle programs, allowing for
failing, non deterministic, and stateful operations.
For example, a C function `u16 square(u8 a)` is represented as
a term of type `u8 ⇒ NonDet u16` in Isabelle.


The value relation is defined automatically (by some ML procedure) for each involved C type in the 
generated C code.
<!-- , using information provided by AutoCorres about the C type at the ML level. -->
When no custom layout is involved, the value relation for a C struct `T` between a value `v` and
a term `t` of type `T` (represented in Isabelle) enforces `v` to be a record 
with the same number of fields as `T`, such 
the field values are them-selves value-related to the corresponding fields of `t`.
The adequacy of this generated value relation relies on the fact that
records are straightforwardly compiled to C records.

### Layouts and the value relation

When specified with a layout `l`, a cogent record `T =  { a : A, b : B }` is compiled (essentially) to an 
array of bytes `⟦ T ⟧ₗ`. Thus, we need to define a value relation for
a C array of bytes, relating a value (in sense of the update semantics) and an array `arr` of bytes.
<!-- The update semantics, as part of the deep embedding, is not aware of the implementation details. -->
The relation should still enforce the value to be a record type with the same
number of fields as in `T`. It should also tell something about the field values, namely
that they should relate to the corresponding data encoded in the array of bytes according
to the layout.

In the example above, the value relation would enforce that the first field of the value
relates to `get_a(arr)`, where `get_a` is the custom getter whose expected type here is
`⟦ T ⟧ₗ ⇒ ⟦ A ⟧`.

### Direct definition of custom getters

AutoCorres provides a definition of the custom getters from the C code, but they have not the
right type for the value relation, as they are monadic. In the example above, it provides
`get_a : ⟦ T ⟧ₗ ⇒ NonDet ⟦ A ⟧`
Defining the value relation as described above thus requires to infer a *direct* definition
 `direct_get_a : ⟦ T ⟧ₗ ⇒ ⟦ A ⟧`.
This is done by a ML procedure which inspects the monadic definition.

They are other possible ways to achieve this goal. For example, the compiler could be extended to
define these direct getters in the generated theory files.


## Get/Set lemmas

The lemmas that are discussed in this section are about custom setters and
getters.
They gather enough evidence for the record lemmas to be successfuly proven.

There are four types of get/set lemmas, schematically summarized as follows:
1. `val_rel x v ⇒ val_rel x (get_a (set_a p v))` (this statement is explained below more carefully)
2. `get_a ∘ set_b = get_a`
3. `C_get = direct_get`
4. `C_set = direct_set`

Here, `direct_get/set` refers to the direct definition of getters/setters mentionned
above, while `C_get/set` refers to the monadic definition generated by 
AutoCorres.
We haven't discussed so far the direct definition of setters. They are inferred by a similar
process as the direct getters.

The first two types of get/set lemmas involve the direct definitions.

The first statement weakens the more intuitive `get_a ∘ set_a = id`,
which is false in case the field is a variant. Indeed, variants are compiled to 
structures packing all the fields for each 
constructor, with an additionnal tag field. Thus, at each stage, only a subset
of these fields is relevant, depending on the tag field. The custom getter must
return such a record, from a given byte array. Suppose it has inferred the tag
from the byte array, following the specified custom layout. The layout describes
how the relevant fields are retrieved from the byte array, but the getter must
provide values for the irrelevant fields as well. What else can it do but
provide arbitrary values for them? But then, the custom getter `get_a` is not surjective, so
there is no hope that `get_a ∘ set_a = id`.

## Evaluation of the complexity of the get/set lemmas
The correspondence between the direct and monadic definitions of getters/setters (last two
statements) does not require much effort.

The automation of the first two statements (especially the first) would probably require 
monthes to complete.
