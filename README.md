This repository contains some simple examples of dargent programs. The goal
is to prove the correspondence between the monadic program (generated by
AutoCorres from the C program) and the update semantics.

# Requirements

- my [branch](https://github.com/amblafont/cogent/tree/dargent-isa) 
`dargentisa` of cogent;
- my [version](https://github.com/amblafont/AutoCorres) of AutoCorres (this 
version fixes an issue that made some C programs systematically fail).

# Make an example

1. `cd` in a subdirectory of an example
2. Compile the example and generate the theory files with the cogent compiler
3. Edit the generated `.table` file so that it matches the specific format
for custom layouts, giving the name of the custom getters/setters
(the compiler should be adapted at some point so that this step is no longer
necessary)
4. Check that the theory file ending with with `_CorresProof.thy` compile.

This theory file indeed attempts to prove the correspondance between the monadic
 and the update semantics.

On my computer, for step 2, I use the command
2. `. ../compiles.sh branch cogent_file`

(branch can be master or dargentisa)
This will generates a directory `build_cogent_file_branch` with all the theory
files in it.


# Status

In principle, any example should work: there is some cheating tactic in the 
generated `_CorresSetup` theory file which automatically prove the get/set
lemmas.
 
The remaining task is to replace this cheating tactic with a proper automatic
proof tactic.

# TODOs

TODO: The C compilation generates useless masks in the parts of the getters for custom layouts
TODO: check examples with different layouts for the same record 
  (I fear a clash in the table file, as the layout is always undefined)
