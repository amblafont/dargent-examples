This directory evaluates whether it is possible to get a full proof of refinement with the seed trick

- [random.c](random.c) is the original C file. It declares a non deterministic function `char rand()` and defines
a main function that calls `rand`. The goal is to write the main function in cogent using the seed
trick to account for non-determinacy, keeping `rand` abstract. Then, we try to get a full refinement proof from
AutoCorres to the shallow embedding

- [random_seed.cogent](random_seed.cogent) is the cogent version using the seed trick. `main` is defined explicitely, while
`rand` is kept abstract (there called `rand_with_seed`)

- [random_seed.ac](random_seed.ac) defines the (dummy) abstract Seed type and implements the abstract function `rand_with_seed` using on the non deterministic 
C `rand()` function.
