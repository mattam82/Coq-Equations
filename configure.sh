#!/usr/bin/env bash

if [ "$1" == "hott" ]
then
    echo "Building HoTT version"
    if command -v hoqc >/dev/null 2>&1
    then coq_makefile -f _HoTTProject -o Makefile
    else echo "Error: hoqc not found in path"
    fi
else
    echo "Building Coq version (default)"
    if command -v coqtop >/dev/null 2>&1
    then coq_makefile -f _CoqProject -o Makefile
    else echo "Error: coqtop not found in path"
    fi
fi