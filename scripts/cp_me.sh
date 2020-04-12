#!/bin/sh

echo Linking `which me` to $1 ...
rm -f $1 && ln -s `which me` $1
