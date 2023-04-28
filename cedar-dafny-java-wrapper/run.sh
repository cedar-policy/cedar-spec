#!/bin/bash
lib_path=$(pwd)
class_path=$(pwd)
main_class="com.amazon.waterford_definitional_engine.Main"

java -Djava.library.path="$lib_path" -cp "$class_path" "$main_class" "$@"
