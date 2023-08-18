#!/bin/sh

if [ "$1" != "pre" ] && [ "$1" != "post" ]; then exit 1; fi

output="$(dirname "$0")/BaseDir.idr"

{
    echo "module BaseDir"
    echo
    echo "import Test.Golden.RunnerHelper"
    echo
    echo "export"
    echo "BaseTestsDir where"

    printf "  baseTestsDir = "

    if [ "$1" = "pre" ]; then echo "\"$(pwd)\""; else echo "?base_tests_dir"; fi
} >"$output"
