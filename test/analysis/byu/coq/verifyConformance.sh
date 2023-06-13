#!/bin/bash
echo "Verifying a chain of n+1 nodes conforms to a chain n nodes."
if coqc MyCHIPsConformance.v; then
  echo "Proof script verified."
else
  echo "ERROR: proof verification failed."
fi

