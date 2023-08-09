#!/bin/bash

SCRIPT_DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )
cd $SCRIPT_DIR
cd ..
#Look through checklist
echo "STARTING CHECKLIST"
while read line; do
  if [[ $line = \#* ]]
  then
	  echo "$line"
  else
	  echo "PROCESS YN FOR" "$line"
  fi
done < ${SCRIPT_DIR}/checklist.txt
exit 1



