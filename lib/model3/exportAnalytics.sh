# Run this after the simulation runs but before it is destroyed
mongoexport --db=mychips --collection=servers --pretty --out=test/sim/local/analytics/servers.json --forceTableScan
mongoexport --db=mychips --collection=lifts --pretty --out=test/sim/local/analytics/lifts.json --forceTableScan
