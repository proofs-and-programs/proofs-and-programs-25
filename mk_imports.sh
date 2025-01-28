#!/bin/bash
set -e
find PfsProgs25/Unit* -name "*.lean" | env LC_ALL=C sort | sed 's/\.lean//;s,/,.,g;s/^/import /' > PfsProgs25.lean
cat Import_tail.lean >> PfsProgs25.lean
