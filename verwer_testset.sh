#!/bin/bash

./gradlew verwerJar

COUNTER=1
for STATES in 2 3 4 5 6 7 8; do
	for LABELS in 2 3 4; do
		for SPLITS in 2 4 8; do
			for INF in 10 20; do
				java -jar build/jars/verwer.jar -s $COUNTER
				echo "Verwer: $COUNTER"
				COUNTER=$((COUNTER + 1))
			done
		done
	done
done
