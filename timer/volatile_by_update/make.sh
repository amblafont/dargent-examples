
if [[ -z $COGENT_DIR ]]; then echo "requires \$COGENT_DIR to be set"; exit; fi

NAME="volatile_by_update"

BUILD_DIR="build"
COGENT_FILE="$NAME.cogent"
AC_FILE="$NAME.ac"

mkdir -p $BUILD_DIR

CONF_FILE="entrypoints.cfg"
NAME_PP="${NAME}_pp_inferred"
if test -f "$NAME.cfg"; then
	CONF_FILE=$NAME.cfg
fi

# BUILD_AC_FILE="${NAME}_$1.ac"
# cp $AC_FILE $BUILD_AC_FILE
# sed -i s#$2.c#$2_$1.c# $BUILD_AC_FILE

export COGENT_LIBGUM_DIR=$COGENT_DIR/cogent/lib

cogent $COGENT_FILE \
    --root-dir=$COGENT_DIR --infer-c-funcs=$AC_FILE  \
    --cpp-args="-std=c99 \$CPPIN -o \$CPPOUT -E -P -I$COGENT_DIR/cogent/lib -O2 -Wno-parentheses -Wno-declaration-after-statement -Wno-unused-variable -Wno-uninitialized" \
    -g --dist-dir=$BUILD_DIR -o $NAME --root-dir=$COGENT_DIR -A \
    --entry-funcs=$CONF_FILE --proof-input-c="$NAME_PP.c" --funused-dargent-accessors

if [[ $? -gt 0 ]]; then exit $?; fi
cp $BUILD_DIR/$NAME.table $BUILD_DIR/${NAME_PP}.table
