#!/usr/bin/env bash

rm -f Makefile.coq Makefile.hott

if [ "$1" == "--enable-hott" ]
then
    if command -v coqtop >/dev/null 2>&1
    then coq_makefile -f _HoTTProject -o Makefile.hott
    else echo "Error: coqtop not found in path"
    fi
fi

if command -v coqtop >/dev/null 2>&1
then coq_makefile -f _CoqProject -o Makefile.coq
else echo "Error: coqtop not found in path"
fi
