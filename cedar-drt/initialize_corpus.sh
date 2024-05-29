#!/bin/bash

# Copyright Cedar Contributors
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#      https://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

# Some fuzz targets expect that an initial corpus will be present when they
# start running. This is important for unstructured fuzzing because it's not
# reasonable to expect that we will find many, if any, valid policies by
# randomly generating bytes (even with coverage guidance).
#
# This script exits cleanly if it doesn't need initialize a corpus, so it's safe
# to run this for all fuzz targets in automation.

shopt -s globstar

print_usage() {
    echo "Initialize the corpus for a single fuzz target:"
    echo "    ./initialize-corpus.sh FUZZ_TARGET_NAME"
    echo "Initialize the corpus for all fuzz targets:"
    echo "    ./initialize-corpus.sh --all"
    exit 1
}

if [ $# -ne 1 ]; then
    echo "Expected exactly one arguemtn, but $# arguments provided."
    print_usage
fi

initialize_corpus() {
  corpus_dir="./fuzz/corpus/$1/"
  mkdir -p "$corpus_dir"
  case "$1" in
  simple-parser|formatter-bytes|convert-policy-cedar-to-json)
    for f in ../cedar/**/*.cedar; do
      # Rename with a uuid because there are multiple `policy.cedar` files
      cp "$f" "$corpus_dir/$(uuidgen)-$(basename "$f")"
    done ;;

  convert-policy-json-to-cedar)
    for f in ../cedar/**/*.cedar.json; do
      cp "$f" "$corpus_dir/$(uuidgen)-$(basename "$f")"
    done ;;

  convert-schema-json-to-human)
    for f in ../cedar/**/*.cedarschema.json; do
      cp "$f" "$corpus_dir/$(uuidgen)-$(basename "$f")"
    done ;;

  convert-schema-human-to-json)
    for f in ../cedar/**/*.cedarschema; do
      cp "$f" "$corpus_dir/$(uuidgen)-$(basename "$f")"
    done ;;

  *)
    echo "Nothing to do for fuzz target $1"
    return ;;
  esac
  echo "Initialized corpus for fuzz target $1"
}

if [ "$1" =  "--all" ] ; then
  cargo fuzz list |
  while read -r target ; do
    initialize_corpus "$target"
  done
  exit 0
fi

if ! ( cargo fuzz list | grep "^$1\$" > /dev/null ) ; then
    echo "Unknown fuzz target: $1"
    print_usage
fi
initialize_corpus "$1"
