#!/bin/bash

./gradlew estimatorJar rtaJar 

COUNTER=1
for STATES in 2 3 4 5 6 7 8; do
	for LABELS in 2 3 4; do
		for SPLITS in 2 4 8; do
			for INF in 10 20; do
				timeout 10s ./rti/rti tests_1/test$COUNTER/verwer/real_train_verwer_40 g > tests_1/test$COUNTER/output_verwer_40
				#echo "./rti/rti tests_1/test$COUNTER/verwer/real_train_verwer g > output"
				#java -jar build/jars/rta.jar -s output > tests_1/test$COUNTER/verwer_automaton
				#java -jar build/jars/estimator.jar -s tests_1/test$COUNTER/verwer_automaton -t tests_1/test$COUNTER/train -c tests_1/test$COUNTER/test > tests_1/test$COUNTER/verwer_estimation
				echo "Counted for: $COUNTER"
				COUNTER=$((COUNTER + 1))
			done
		done
	done
done
