npx prettier --write . 
npm run tsc
cd ./test/sim/
export PATH="$(pwd)/../../node_modules/.bin:$PATH"
export NODE_DEBUG=debug
./simdock startup
sleep 30
# ./simdock ticket 0 # breaks on the new version
./simdock start sim --runs=10