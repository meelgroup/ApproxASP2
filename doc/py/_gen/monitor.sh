#!/bin/bash

cd "$(dirname "$0")/.."
export BUNDLE_PATH=$(pwd)/.gem
bundle install
bundle exec jekyll serve -l &
trap "kill $!" EXIT
cd _gen

inotifywait -rme ATTRIB --format "%f" . ../../../build/release/bin/python | while read file; do
    case "$file" in
        *.py)
            ;&
        *.mako)
            ;&
        *.so)
            sleep 1
            python3 gen.py
            ;;
    esac
done
