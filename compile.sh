
COGENT_PATH=~/cogent/branches/$1
BUILD_DIR=build_$2
mkdir -p $BUILD_DIR
$COGENT_PATH/cogent/.stack-work/dist/x86_64-linux-tinfo6/Cabal-2.4.0.1/build/cogent/cogent $2.cogent -g --dist-dir=$BUILD_DIR -o $2_$1 --root-dir=$COGENT_PATH -A  --entry-funcs=entrypoints.cfg --fake-header-dir=$COGENT_PATH/cogent/lib/
