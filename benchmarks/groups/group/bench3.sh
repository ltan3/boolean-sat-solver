#!/bin/bash

# SAT

START=$(date +%s)
c=0
s=0
w=0

echo "SHOULD BE UNSAT"

for i in `cat name5`; do
		python3 ../../../dpll.py ../../bench3/$i > results 2>&1
		if grep -q "unsat" results; then
		  echo "$i Pass!"
			let "c+=1"
			let "s+=1"
	  else
      echo "$i Wrong!"
			let "s+=1"
			let "w+=1"
	  fi
		
		rm -f results
done

echo "-------- Your Result --------"
echo "Pass: $c/$s"

END=$(date +%s)
DIFF=$((  $END - $START ))
echo "Took $DIFF seconds."
