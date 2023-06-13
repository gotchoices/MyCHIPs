#!/bin/bash
echo "Beginning analysis."
cd ./spin
echo "Verify Properties hold on Full Model"
./verifyFullModel.sh
echo "Beginning verification of inductive proof"
echo "Verifying properties hold on minimal base case"
./verifyMinimalModel.sh
cd ../coq
./verifyConformance.sh
echo "Inductive Step Proven"
echo "Verifying Coq implementation matches Spin implementation"
cd ../spin
./verifyCoqMapping.sh
echo "Verification complete."

