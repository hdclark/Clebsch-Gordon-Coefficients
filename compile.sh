#!/bin/bash

instructions=" g++ $@ Clebsch-Gordon_Tidy.cc -lm -o cgc "

echo "${instructions}"

${instructions}
