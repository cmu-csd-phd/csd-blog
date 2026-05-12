#! /bin/sh

git checkout "main" || exit 1
git pull || exit 2

cd website/ || exit 255
../binaries/use_zola build

# make image urls use absolute paths for the CSD TV screens
# only needed when generating the live site, local builds don't need this
find . -path "./*/20*/index.html" -exec ../fix-image-paths.py "{}" \;

rm -f ../generated-website.zip
zip -r ../generated-website.zip public/
cd ../

echo "generated-website.zip has been generated. Please put this onto AFS at the right location (/afs/cs.cmu.edu/project/csd-phd-blog/www)."
