#!/bin/bash

SCRIPT_DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )
cd $SCRIPT_DIR
cd ..
#Look through checklist
echo "STARTING CHECKLIST"
while read -u 10 line; do
  if [[ $line = \#* ]]
  then
	  echo "$line"
  else
		while read -u 1 -p "Did you check: ${line}? " yn
		do
								case $yn in
						[Yy]* ) break;;
						[Nn]* ) echo >&2 "Maunual Test Failed: ${line}"; exit 1;;
						* ) echo "Please answer yes or no.";;
				esac
		done
  fi
done 10< ${SCRIPT_DIR}/checklist.txt
exit 0 #ALL TESTS PASSED PROCEED



