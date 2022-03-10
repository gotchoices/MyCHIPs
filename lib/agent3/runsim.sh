npm run tsc
cd ./test/sim/
./simdock startup
sleep 30
./simdock ticket 0
./simdock start sim --runs=10