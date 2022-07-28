# sudo chmod -R 777 test/sim/local/ # Maybe this is only a problem on WSL?
npx prettier --write . 
npm run tsc
cd ./test/sim/
export PATH="$(pwd)/../../node_modules/.bin:$PATH"
export NODE_DEBUG=debug
./simdock startup
sleep 30
./simdock tickets
./simdock start sim --runs=50 