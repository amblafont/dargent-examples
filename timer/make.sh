COGENT_PATH=~/cogent/branches/$1
BUILD_DIR=build_$2
AC_FILE=$BUILD_DIR/$2_$1.ac
mkdir -p $BUILD_DIR
CONF_FILE=entrypoints.cfg
NAME_PP=$2_$1_pp_inferred
if test -f "$2.cfg"; then
	CONF_FILE=$2.cfg
fi

cp $2.ac $AC_FILE
sed -i s#$2.c#$2_$1.c# $AC_FILE
# sed -i s#$2.c#$BUILD_DIR/$2_$1.c# $AC_FILE

$COGENT_PATH/cogent/.stack-work/dist/x86_64-linux-tinfo6/Cabal-2.4.0.1/build/cogent/cogent $2.cogent --root-dir=$COGENT_PATH --infer-c-funcs=$AC_FILE  \
	 --cpp-args="-std=c99 \$CPPIN -o \$CPPOUT -E -P -I$COGENT_PATH/cogent/lib -O2 -Wno-parentheses -Wno-declaration-after-statement -Wno-unused-variable -Wno-uninitialized" \
-g --dist-dir=$BUILD_DIR -o $2_$1 --root-dir=$COGENT_PATH -A  --fake-header-dir=$COGENT_PATH/cogent/lib/ --entry-funcs=$CONF_FILE --proof-input-c="$NAME_PP.c" --funused-dargent-accessors

cp $BUILD_DIR/$2_$1.table $BUILD_DIR/$NAME_PP.table

