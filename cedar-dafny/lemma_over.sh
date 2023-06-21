#!/bin/bash
#
# A utility to extract and compare the lemmas over the 10,000,000 resource unit
# threshold from the statistics dumped by `make GEN_STATS=1`.
#
# To view the lemmas currently over the threshold:
#
#     make GEN_STATS=1
#     ./lemmas_over.sh
#
# To compare the change in lemmas over the treshold after a code change:
#
#     make GEN_STATS=1
#     ./lemmas_over.sh > over.csv
#     make GEN_STATS=1
#     ./lemmas_over.sh --diff over.csv

# Extract the lemmas over the threshold.
function lemmas_over() (
  if [ ! -d TestResults ]; then
    (
      echo 'Error: TestResults directory not found.'
      echo 'You must run make GEN_STATS=1 before executing this script to populate the directory.'
    ) >&2
    exit 1
  fi

  find TestResults -name "*.csv" -exec awk -F ',' 'NR > 1 && $4 > 10000000' {} \;
)

# Diff the lemma names in two csv files with rows formated as dumped by Dafny.
# Expected to be used with files that have already been filtered to contain
# lemmas over the resource unit threshold.
#
# If one argument is provided, diff that file with the lemmas over the resource
# unit threshold currently in `TestResults`. If two arguemnts are provided,
# diff the contents of these files.
function diff_over() {
  function select_lemma_names() ( cut -d',' -f 1 "$1" | sort )

  if [ -z "$1" ]; then
    echo 'Error: You must provide a file to compare with the current lemmas over the threshold.' >&2
    exit 1
  fi

  diff -y \
    <(select_lemma_names "$1") \
    <(select_lemma_names <(if [ -z "$2" ]; then lemmas_over ; else cat "$2" ; fi))
}

if [ "$1" == "-d" ] || [ "$1" == "--diff" ] ; then
  shift
  diff_over "$@"
else
  lemmas_over "$@"
fi
