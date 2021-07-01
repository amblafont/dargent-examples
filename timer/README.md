Timer driver

Files
- `meson_timer.c` and `meson_timer.h`: original C driver
- `ignore_volatile_variant.cogent`, `ignore_volatile_variant.ac`: cogent driver
- `TimerSpec.thy`: abstract driver
- `RefinementVariant.thy`: proof that the shallow embedding of the cogent driver refines the abstract driver

To compile, use 
- the dargentfull branch of cogent https://github.com/amblafont/cogent/tree/dargentfull
- a custom branch of autocorres:   https://github.com/amblafont/AutoCorres

1. `mkdir -p build_ignore_volatile_variant/` 
2. `cp ignore_volatile_variant.ac build_ignore_volatile_variant/ignore_volatile_variant_dargentfull.ac`
3. `sed -i s#ignore_volatile_variant.c#ignore_volatile_variant_dargentfull.c# build_ignore_volatile_variant/ignore_volatile_variant_dargentfull.ac`
4. `cogent ignore_volatile_variant.cogent  \
      --root-dir=/path/to/cogent/repo \
      --fake-header-dir=/path/to/cogent/repo/cogent/lib/  \
      --cpp-args="-std=c99 $CPPIN -o $CPPOUT -E -P -I/path/to/cogent/repo/cogent/lib -O2 -Wno-parentheses -Wno-declaration-after-statement -Wno-unused-variable -Wno-uninitialized" \
      --infer-c-funcs=build_ignore_volatile_variant/ignore_volatile_variant_dargentfull.ac  \
      -g  \
      --dist-dir=build_ignore_volatile_variant  \
      -o ignore_volatile_variant_dargentfull  \
      -A  \
      --entry-funcs=entrypoints.cfg  \
      --proof-input-c="ignore_volatile_variant_dargentfull_pp_inferred.c"  \
      --funused-dargent-accessors`

