
This document reports on my understanding and attempts to extend the 
(formalisation of the) type system with dargent.


Roughly, dargent affects the well-formed predicate on types (types with
bad layouts will be rejected). The value or update semantics can be left
unchanged.

In a first section I explain what I call the **preservation property*** 
that the type system loses when
introducing dargent (at least as it is presented in the write-up).

Here are the options that I consider:
1. leave the formalisation of the type system for later (and rather focus on 
writing a convincing example with Dargent): present Dargent
as a way to control the C code generation, leaving everything else the same;
2. leave layout polymorphism out of the formalisation;
3. formalise the type system without the preservation property;
4. Try to figure out a type system keeping the preservation property
(See the last subsection of the section about the failure of the preservation
property, for a possible solution).


# Failure of the preservation property

One important property of the type system on which the formalisation heavily
relies on is that if a type `τ` is well-formed, then so is any well-formed instantiation 
`τ[t/α]`, where `α` is a type variable and `t` is a well-formed type. 


Such a property is lost with dargent, at least according to the **polymorphic rule** of figure
8 in the writeup:
```
typeOf(f)= ∀ α β.C ⇒ T             Q ⊢  C[τ/α, l/β]
---------------------------------------------------
   Q ⊢ f τ l : T[τ/α, l/β]
```
where 
- α is a type variable and τ a type;
- β is a layout variable and l a layout;
- `C` is a list of constraints, which are of the shape `α : κ` or 
`β ~ τ`, where κ is a set of kinds;
- T is a type of the shape `t → u`.

## A problematic example

Consider now the example of a polymorphic function `f` of type `∀ α. C ⇒ 
t layout { a : 1b at 0b} → …`. Then, `f U8 ` has type
`U8 layout { a : 1b at 0b} → …` which obviously is ill-formed.
But there is no constraint that we can think to put in `C` such that the 
the check `Q ⊢ C[U8/t]` would not pass.

## Solution in the compiler

This is not a problem in the compiler, because it checks anyway that all the
involved types (in particular, `T[τ/α, l/β]`) are well-formed (although this is not explicit in the rule
above). In the formalisation, however, everything must be explicit.
Without dargent, it was enough to add the premise that `T` was well-formed,
since then `T[τ/α]` would be, by preservation of wellformedness.

## Solution 1: constraints `l ~ α`

A first solution to the problematic example above is to allow constraints 
of the shape `l ~ α`, where `l` could be any layout (not only a variable): 
in the example above, clearly the constraint ` {a : 1b at 0b} ~ U8` would not be satisfied.

## The overlapping problem
However this extension of constraints does not address another issue.
One may hope that the constraints `β ~ τ` would at least ensure that `T[ℓ/β]`
is always wellformed if `T` is. But this is not the case, for `ℓ` may overlap
with some other layout. For example, consider `T = { a : Bool, b : Bool} layout
{a : 1b at 0b, b : β} → … `. Then, `T[1b at 0b / β]` results in an illformed
type `{ a : Bool, b : Bool} layout {a : 1b at 0b, b : 1b at 0b}`, although
the constraint `1b at 0b ~ Bool` is satisified. 

## Solution 2: constraints `l ~ t`

Another solution is to allow constraints relating a layout and a type, even if
none of them are variables. The overlapping problem in the example above
disappears by introducing the constraint `{a : 1b at 0b, b : β} ~ {a : Bool, b : Bool}`.
in C.


# Option 2: Dropping layout polymorphism
Leaving layout polymorphism out of the scope gets rid of the overlapping problem,
and with the first constraint extension `l ~ α` proposed above, preservation of wellformedness
is recovered.

# Option 3: Formalise the type system without the preservation property

This is what I am trying now, but a lot of the formalised lemmas seem to rely
on this property. Some important statements may need to be rephrased,
such as the one about preservation of typing for the value and update semantics
(since they involve instantiation of types).

In the polymorphic typing rule mentioned above, I add the premise that 
`T[τ/α, l/β]` is well-formed. But then, do I need to keep the premise that
`T` is well-formed?



# Personal (French) comments 

Je dois prouver une loi de substitution (associativite) pour les layouts, et ca m'oblige a introduire
un environnement.

