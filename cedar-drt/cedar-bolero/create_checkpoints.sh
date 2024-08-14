#!/bin/bash

# Check if directory argument is provided
if [ -z "$1" ]; then
    echo "Usage: $0 <directory>"
    exit 1
fi

dir="$1"

# Create queue directories
for i in {0..11}; do mkdir "queue_$i"; done

# Find earliest modified file
earliest_file=$(ls -rt "$dir" | head -n 1)
earliest_mod_time=$(date -r "$dir/$earliest_file" +%s)

# Copy files to queue directories
for file in "$dir"/*; do
    mod_diff=$(($(date -r "$file" +%s) - $earliest_mod_time))
    mod_hours=$((mod_diff / 3600))
    for i in $(seq 0 "$mod_hours"); do
        cp "$file" "queue_$i"
    done
done
