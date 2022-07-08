COGENT_PATH=~/cogent
COGENT_PATH_BIN=cogent
FILE=random_seed

BUILD_DIR=build_$FILE
mkdir -p $BUILD_DIR
CONF_FILE=entrypoints.cfg
if test -f "$FILE.cfg"; then
	CONF_FILE=$FILE.cfg
fi


# sed -i s#$FILE.c#$BUILD_DIR/$FILE.c# $AC_FILE


$COGENT_PATH_BIN $FILE.cogent -g --dist-dir=$BUILD_DIR -o $FILE --root-dir=$COGENT_PATH -A  --entry-funcs=$CONF_FILE --fake-header-dir=$COGENT_PATH/cogent/lib/ 

C_FILE=$FILE.c
C_GENERATED_FILE=$FILE_generated.c

mv $BUILD_DIR/$C_FILE $BUILD_DIR/$C_GENERATED_FILE
cp $FILE.ac $BUILD_DIR/$C_FILE
sed -i .bak s#$FILE.c#$C_GENERATED_FILE# $BUILD_DIR/$C_FILE
