#!/usr/bin/env bash

rm -f Makefile.rocq Makefile.hott

if [ "$1" == "--enable-hott" ]
then
    if command -v rocq >/dev/null 2>&1
    then rocq makefile -f _HoTTProject -o Makefile.hott
    else echo "Error: rocq not found in path"
    fi
fi

if command -v rocq >/dev/null 2>&1
then rocq makefile -f _CoqProject -o Makefile.rocq
else echo "Error: rocq not found in path"
fi
