#!/usr/bin/env bash

if [ -d Equations-HoTT ]
then
    echo "Equations-HoTT already built"
else
    git clone -b cumulative-paths git@github.com:mattam82/HoTT.git Equations-HoTT
    cd Equations-HoTT
    rm -rf .git
    ./autogen.sh
    ./configure
    make
    cd ..
fi