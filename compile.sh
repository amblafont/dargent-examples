
BUILD_DIR=build_$2
mkdir -p $BUILD_DIR
cogent $2 -g --dist-dir=$BUILD_DIR -o $2_$1 --root-dir=$COGENT_PATH -A  --entry-funcs=entrypoints.cfg --fake-header-dir=$COGENT_PATH/cogent/lib/
