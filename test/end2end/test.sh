exec="_build/default/bin/main.exe"

for file in tests/*.ml 
do
	dune exec simple_tester $exec $file
done
