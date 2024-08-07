#!/bin/bash -e

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

# Builds the CLI and then checks that it runs without error for all sample JSON inputs.

lake build Cli

cli_exe=./.lake/build/bin/Cli

failed=0
check_cli() {
  local cmd="$1"
  local json="$2"
  echo -n "$json "
  if ! ( $cli_exe $cmd "$json" | jq --exit-status 'has("ok")' ) ; then
    failed=1
  fi
}

echo Testing CLI authorize
for f in ./Cli/json-inputs/authorize/* ; do
  check_cli authorize "$f"
done

echo
echo Testing CLI validate
for f in ./Cli/json-inputs/validate/* ; do
  check_cli validate "$f"
done

exit $failed
