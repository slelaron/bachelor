#!/bin/bash

./gradlew testerJar

SOLUTION_COUNTER=1
for TRAIN in 10 15 20 25 30 35 40; do
	COUNTER=1
	for STATES in 2 3 4 5 6 7; do
		for LABELS in 2 3 4 5; do
			for SPLITS in 5 10; do
				for INF in 10 20 30 40 50 100; do
					timeout 15m time java -jar build/jars/tester.jar -i $INF -s $COUNTER -t $TRAIN -sn $SOLUTION_COUNTER
					echo "Tested: $((288 * SOLUTION_COUNTER - 288 + COUNTER)) of 2016"
					COUNTER=$((COUNTER + 1))
				done
			done
		done
	done
	SOLUTION_COUNTER=$((SOLUTION_COUNTER + 1))
done
