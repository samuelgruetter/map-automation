#!/bin/sh

F=./maps_v0.v

sed -n '/BEGIN LEMMAS/,$p' $F > saved.v

SRC=../bedrock2/compiler/src

FILES="$SRC/../lib/fiat_crypto_tactics/Test.v
       $SRC/../lib/fiat_crypto_tactics/Not.v
       $SRC/../lib/LibTacticsMin.v
       $SRC/Decidable.v
       $SRC/util/Tactics.v
       $SRC/util/Set.v
       $SRC/util/Map.v
       $SRC/util/MapSolverTest.v"

for f in $FILES; do
    printf '\n(* ** %s *)\n' $f
    cat $f
done | sed -E -e 's/Require.* (compiler|lib)\..*/(* \0 *)/g' > $F

printf '\n\n' >> $F

cat saved.v >> $F

rm saved.v

coqc $F
