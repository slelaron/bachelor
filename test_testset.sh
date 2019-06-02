#!/bin/bash

./gradlew testerJar

#SOLUTION_COUNTER=3
#for TRAIN in 30 40 50 60; do
	COUNTER=1
	for STATES in 2 3 4 5 6 7 8; do
		for LABELS in 2 3 4; do
			for SPLITS in 2 4 8; do
				for INF in 10 20; do
					#if [ $COUNTER -ge 39 ]; then
						timeout 15m time java -jar build/jars/tester.jar -v -i $INF -s $COUNTER -t 1000 -sn 100
						#echo "Tested: $((126 * SOLUTION_COUNTER - 126 + COUNTER))"
						echo "Tested: $((COUNTER))"
					#fi
					COUNTER=$((COUNTER + 1))
				done
			done
		done
	done
	#SOLUTION_COUNTER=$((SOLUTION_COUNTER + 1))
#done
