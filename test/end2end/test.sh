#!/bin/bash

if [[ -z "$1" ]]
then
	echo "USAGE: $0 <cwd>"
	exit 1
fi

cwd="$1"
exec="$cwd/_build/default/bin/main.exe"
tester="$cwd/_build/default/test/end2end/simple_tester.exe"


if [[ -z `find "$cwd/test/end2end/tests/" -name '*.lm'` ]]
then
	echo "no tests found"
	exit 0
fi

for file in `find "$cwd/test/end2end/tests/" -name '*.lm' | sort`
do
	$tester $exec $file
done
