#!/usr/bin/env bash

for dir in `ls .`; do
    if [ $dir != 'temp' ]; then
        echo $dir
        for file in `cd $dir; ls *.v`; do
            mv $dir/$file $dir/${file}_backup
            mv temp/$file $dir/$file
        done
    fi
done
