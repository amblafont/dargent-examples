
COGENT_PATH=/home/laf027/cogent/branches/$1
mkdir -p build
$COGENT_PATH/cogent/.stack-work/dist/x86_64-linux/Cabal-2.4.0.1/build/cogent/cogent $2.cogent -g --dist-dir=build -o $2_$1 --root-dir=$COGENT_PATH -A  --entry-funcs=entrypoints.cfg --fake-header-dir=$COGENT_PATH/cogent/lib/
