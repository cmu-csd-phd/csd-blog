#! /bin/sh

ROOT=../generated-website
ZIP=$ROOT-$(date '+%Y-%m-%d').zip

git checkout "main" || exit 1
git pull || exit 2

cd website/ || exit 255
../binaries/use_zola build

# make image urls use absolute paths for the CSD TV screens
# only needed when generating the live site, local builds don't need this
find . -path "./*/20*/index.html" -exec ../fix-image-paths.py "{}" \;

rm -f $ROOT*
zip -r "$ZIP"  public/
cd ../

echo "$ZIP has been generated. Please put this onto AFS at the right location (/afs/cs.cmu.edu/project/csd-phd-blog/www)."
