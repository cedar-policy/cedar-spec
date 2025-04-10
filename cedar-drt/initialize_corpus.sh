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
    echo "Expected exactly one argument, but $# arguments provided."
    print_usage
fi

initialize_corpus() {
  corpus_dir="./fuzz/corpus/$1/"
  mkdir -p "$corpus_dir"

  # Copy over seeds
  seed_dir="./fuzz/seeds/$1"
  if test -d $seed_dir; then
    echo "Copying seeds for fuzz target $1"
    cp -r "$seed_dir"/. "$corpus_dir"
  fi

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

  convert-schema-json-to-cedar)
    for f in ../cedar/**/*.cedarschema.json; do
      cp "$f" "$corpus_dir/$(uuidgen)-$(basename "$f")"
    done ;;

  convert-schema-cedar-to-json)
    for f in ../cedar/**/*.cedarschema; do
      cp "$f" "$corpus_dir/$(uuidgen)-$(basename "$f")"
    done ;;

  roundtrip-entities-bytes)
    for f in ../cedar/**/entity.json; do
      cp "$f" "$corpus_dir/$(uuidgen)-$(basename "$f")"
    done
    for f in ../cedar/**/entities.json; do
      cp "$f" "$corpus_dir/$(uuidgen)-$(basename "$f")"
    done ;;

  datetime-parser-drt)
    sed -En 's/test(Inv|V)alidDatetime "([^"]*)".*/\2/p' ../cedar-lean/UnitTest/Datetime.lean |
    while read p ; do
      echo "$p" > "$corpus_dir/$(uuidgen)"
    done ;;

  duration-parser-drt)
    sed -En 's/test(Inv|V)alidDuration "([^"]*)".*/\2/p' ../cedar-lean/UnitTest/Datetime.lean |
    while read p ; do
      echo "$p" > "$corpus_dir/$(uuidgen)"
    done ;;

  ip-parser-drt)
    sed -En 's/test(Inv|V)alid "([^"]*)".*/\2/p' ../cedar-lean/UnitTest/IPAddr.lean |
    while read p ; do
      echo "$p" > "$corpus_dir/$(uuidgen)"
    done ;;

  decimal-parser-drt)
    sed -En 's/test(Inv|V)alid "([^"]*)".*/\2/p' ../cedar-lean/UnitTest/Decimal.lean |
    while read p ; do
      echo "$p" > "$corpus_dir/$(uuidgen)"
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
