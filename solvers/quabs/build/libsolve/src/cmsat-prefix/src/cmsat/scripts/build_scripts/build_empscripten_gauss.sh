#!/bin/bash

set -e

rm -rf cm* CM* lib* cryptomini* Testing* tests* pycryptosat include tests cusp* scalmc*
cmake -DENABLE_PYTHON_INTERFACE=OFF -DNOM4RI=ON \
    -DENABLE_TESTING=OFF -DNOZLIB=ON -DONLY_SIMPLE=ON \
    -DEMSCIPTEN=ON -DUSE_GAUSS=ON\
    -DCMAKE_TOOLCHAIN_FILE=/home/soos/development/emsdk/emscripten/1.38.0/cmake/Modules/Platform/Emscripten.cmake \
    ..
make VERBOSE=1 -j4
