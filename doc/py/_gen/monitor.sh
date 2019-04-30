cd "$(dirname "$0")/.."
jekyll serve &
trap "kill $!" EXIT
cd _gen
inotifywait -e DELETE_SELF templates/html.mako ../../../build/*/bin/python/clingo*.so -m | while read file action; do
    python gen.py
done
