#!/bin/bash
cd "$1" || { printf 'unable to navigate to target\n' >&2; exit 1 ; }
for file in *.out; do
    test -f "$file" || continue
    printf "$file "
    awk '{print "    "$NF}' "$file" | awk '{ sum += $1 } END { print sum }'

done
