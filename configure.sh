#!/usr/bin/env bash

rm -f Makefile.coq Makefile.HoTT

if [ "$1" == "HoTT" ]
then
    if command -v hoqc >/dev/null 2>&1
    then echo "Equations is incompatible with HoTT for Coq version 8.9 and below, please upgrade to Coq 8.10"
    else echo "Error: hoqc not found in path"
    fi
else
    echo "Building Coq version (default)"
    if command -v coqtop >/dev/null 2>&1
    then coq_makefile -f _CoqProject -o Makefile.coq
    else echo "Error: coqtop not found in path"
    fi
fi