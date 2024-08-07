#!/bin/bash

cwd="`pwd`"
exec="$cwd/_build/default/bin/main.exe"
tester="$cwd/_build/default/test/simple_tester.exe"

function get_expected() {
	code="`grep "//@code:" "$1" | sed -E 's/[^0-9]*//g' | tail -n 1`"
	if [[ -z "$code" ]]; then
			echo 0
	else
			echo "$code"
	fi
}

if [[ -z `find "$cwd/test/tests/" -name '*.lm'` ]]
then
	echo "no tests found"
	exit 0
fi

dune build

echo "==========[ Testing Normal analysis ]=========="
for file in `find "$cwd/test/tests/" -name '*.lm' | sort`
do
	# $tester $exec $file --no-print-stats
	out="`$exec $file 2&>1`"
	exit="$?"
	expected_exit="`get_expected $file`"
	# this still doesn't work if test specyfies that it fails
	if [[ "$exit" -ne "$expected_exit" ]]
	then
		echo "expected: $expected_exit, and got: $exit"
		echo "[FAILED]: $file"
		echo $out
	fi
done

echo
echo "==========[ Testing Crude analysis ]=========="
for file in `find "$cwd/test/tests/" -name '*.lm' | sort`
do
	# $tester $exec $file --no-print-stats --crude-analysis
	expected_exit="`get_expected $file`"
	out="`$exec --crude-analysis $file 2>&1`"
	exit="$?"
	# echo "expected: $expected_exit, and got: $exit"
	if [[ "$exit" -ne "$expected_exit" ]]
	then
		echo "[FAILED]: $file"
		echo $out
	fi
done


