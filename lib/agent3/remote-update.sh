#!/bin/bash
ssh -i "lib/mychips-capstone-keys.pem" ec2-user@ec2-52-11-235-129.us-west-2.compute.amazonaws.com "cd mychips; git checkout capstone-sim-dev; git pull; ./simdock startup"
