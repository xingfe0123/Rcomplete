#!/bin/bash
source ~/.opam/default/init.sh > /dev/null 2>&1
cd /Users/luoxing/coq/seq
coqc SeriesAlgebra.v 2>&1
