typedef struct Seed {
  int dummy;
} Seed;


#include "random_seed_generated.c"

char rand ();

SeedValue rand_with_seed(Seed * s) {

   // s->dummy = s->dummy + 1 ?

   SeedValue r = 
      // what else?
      { .seed = s, 
        .value = rand() };

   return r;
}
