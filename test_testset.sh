#!/bin/bash

./gradlew testerJar

SOLUTION_COUNTER=100
COUNTER=1
for SOURCE in 116 117 118 119 120 121 122 123 124 125 126; do
	echo "Start: $SOURCE"
	timeout 15m time java -jar build/jars/tester.jar -s $SOURCE -t 1000 -sn $SOLUTION_COUNTER -v
	echo "End: $SOURCE"
	echo "Tested: $((126 * SOLUTION_COUNTER - 126 + COUNTER))"
done
SOLUTION_COUNTER=$((SOLUTION_COUNTER + 1))
