#!/bin/zsh
# usage: ./mk.sh OC/Basic   -- compiles OC/Basic.lean to build/OC/Basic.olean
cd "$(dirname "$0")"
LP="$(cat .leanpath):$(pwd)/build"
mkdir -p "build/$(dirname $1)"
env LEAN_PATH="$LP" lean --root=. -o "build/$1.olean" "$1.lean"
