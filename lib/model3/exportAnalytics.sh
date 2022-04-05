# Run this after the simulation runs but before it is destroyed
mongoexport --db=mychips --collection=servers --pretty --out=test/sim/local/analytics/servers.json --forceTableScan
