#!/bin/bash

cd "$(dirname "$0")/.."
jekyll serve -l &
trap "kill $!" EXIT
cd _gen

inotifywait -rme ATTRIB --format "%f" templates ../../../build/release/bin/python | while read file; do
    case "$file" in
        *.mako)
            ;&
        *.so)
            sleep 1
            python3 gen.py
            ;;
    esac
done
