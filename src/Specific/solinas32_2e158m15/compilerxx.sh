#!/bin/sh
set -eu

g++ -march=native -mtune=native -std=gnu++11 -O3 -flto -fomit-frame-pointer -fwrapv -Wno-attributes -Dmodulus_limbs='6' -Dmodulus_bytes_val='26 + 1/3' -Dlimb_t=uint32_t -Dlimb_weight_gaps_array='{27,26,26,27,26,26}' -Dmodulus_array='{0x3f,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xf1}' -Dq_mpz='(1_mpz<<158) - 15' "$@"