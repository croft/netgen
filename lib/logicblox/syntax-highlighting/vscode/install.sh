#!/usr/bin/env bash

set -e

EXTENSION_DEST=~/.vscode/extensions/logicblox
EXTENSION_SRC=$(dirname $0)

rm -rf $EXTENSION_DEST
mkdir -p $EXTENSION_DEST
cp -Lr $EXTENSION_SRC $EXTENSION_DEST
