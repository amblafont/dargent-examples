With custom layouts, the value relation relies on custom getters.
Consider the example of a record with two fields. Typically, the value relation
looks like:
```
 val_rel uv x ≡ 
     ∃a b. uv = URecord [a, b] ∧ val_rel (fst a) 
(custom_get_a x) ∧ val_rel (fst b) (custom_get_b x)"
```
where `custom_get_a` and `custom_get_b` are the custom accessors
(dependent on the layout).

These accessors must thus be defined in Isabelle.
Then, a number of lemmas must be proven :
1. `get o set = id`
2. `get_a o set_b = get_a`
3. `C_get = isabelle_get`
4. `C_set = isabelle_set`

In fact, we don't need to know more about the isabelle getters for the 
correspondence lemma. Thus, this opens the door for extremely customised
layouts, where the user would not specify the layout but provides directly
the getters/setters together with these lemmas.

Here are some possible strategies for generating these Isabelle getters:
1. write a ML function, with C getter code as input
2. write a ML function, with custom layout as input
3. make the cogent compiler generate them

I think that the choice of the strategy would affect strongly the proof 
automation of the above mentionned lemmas.

1. The first strategy is already implemented:

- drawback: the compiler does not always generate all the getters, if they are 
not used.
+ advantage: the Isabelle getter is close to the C getter code. It is thus
 easier to show that they correspond.

We could modify the compiler so that it always generate the getters.
However, it would uncessarily increase the size of the generated C code,
  and parsing big C files into Isabelle can be extremely slow.

This could be a temporary solution (but as mentionned above, changing
the strategy afterwards may require a lot of work to adapt the proof
automation of the above mentionned lemmas)

2. The second strategy has the disadvantage that it will be harder to
maintain the proof of correspondence between C getters and Isabelle 
getters, because they are generated independantly.

3. The third strategy has the advantage that it will be easy to maintain 
the similarity between the isabelle getter code and the C getter code
(thus it will be easier to show that they correspond).


