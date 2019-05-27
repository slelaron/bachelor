#!/bin/bash

./gradlew generatorJar

COUNTER=1
for STATES in 2 3 4 5 6 7; do
	for LABELS in 2 3 4 5; do
		for SPLITS in 5 10; do
			for INF in 10 20 30 40 50 100; do
				java -jar build/jars/generator.jar -n $STATES -s $SPLITS -l $LABELS -atb $INF -ttb $INF -t $COUNTER
				echo "Generated: $COUNTER"
				COUNTER=$((COUNTER + 1))
			done
		done
	done
done
