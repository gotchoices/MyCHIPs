#!/bin/bash
#
ROOT_DIR=$(git rev-parse --show-toplevel)
GIT_HOOKS_DIR="${ROOT_DIR}/.git/hooks"
LINKED_HOOKS_DIR="${ROOT_DIR}/githooks"

#Create symbolic link
ln -s "${LINKED_HOOKS_DIR}/pre-push" "${GIT_HOOKS_DIR}/pre-push"
echo "Symbolic Link added to ${LINKED_HOOKS_DIR}/pre-push from ${GIT_HOOKS_DIR}/pre-push"
