#!/bin/sh
export FM=$PWD/ForMani

cd SatELite
make realclean
make r
cp SatELite_release ../../SatElite
cd ..
