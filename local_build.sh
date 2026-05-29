#! /bin/sh

cd website/ || exit 255
../binaries/use_zola build
rm -f ../generated-website.zip
zip -r ../generated-website.zip public/
cd ../
