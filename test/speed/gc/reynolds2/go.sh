#!/bin/sh

fosterc reynolds2-subheaps-smarter.foster -o reynolds2-subheaps-smarter.exe --backend-optimize --asm --show-cmdlines
cperfstat ./reynolds2-subheaps-smarter.exe --foster-compaction-threshold 99999 --foster-disable-sticky
vim gclog.txt
