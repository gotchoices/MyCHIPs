## Analysis done by graduate students at Brigham Young University

# Model Checking
We utilize SPIN to verify safety and liveness properties of the MyCHIPs lift protocol using a small example with only 2 entities participating in the lift and one node serving as referee. This serves as a base case for an inductive proof that shows these properties hold for a MyCHIPs system of arbitrarily many entities.

# Coq Proof
We utilize Coq for machine checked proofs that prove that the properites verified in the model checking step continue to hold as more entities are added to the system. We do this by showing conformance, as defined by Dill in Trace Theory, between the larger system and the verified base case.

The helper script 
./verifyMyCHIPs.sh is provided to execute each of analysis and print the results

The Dockerfile in this directory provides an envirornement that is sufficient to run the analysis.
