cd "$(dirname "$0")/.."
jekyll serve &
trap "kill $!" EXIT
cd _gen
while inotifywait -e DELETE_SELF templates/html.mako ../../../build/*/bin/python/clingo*.so; do
    python gen.py
done
