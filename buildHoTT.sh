#!/usr/bin/env bash

if [ -d Equations-HoTT ]
then
    echo "Equations-HoTT already built"
else
    git clone -b cumulative-paths http://github.com/mattam82/HoTT Equations-HoTT
    cd Equations-HoTT
    rm -rf .git
    ./autogen.sh
    ./configure
    make
    cd ..
fi