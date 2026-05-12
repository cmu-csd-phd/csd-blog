#! /bin/sh

if [ "$#" -ne 1 ]; then
  echo "Usage: $0 PULL-REQUEST-ID" >&2
  exit 1
fi

git checkout main && git pull origin main || exit 1
git fetch origin "pull/${1}/head:pr-${1}" || exit 2
git checkout "pr-${1}" || exit 3
git pull origin "refs/pull/${1}/head" || exit 4
git merge origin/main --no-edit --no-commit || exit 5

cd website/ || exit 255
../binaries/use_zola serve
cd ../
