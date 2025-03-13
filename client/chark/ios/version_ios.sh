#!/bin/bash
#Get the current version and build from package.json, install in ios build files
#Writes to ios/chark/Config.xcconfig, must configure xcode to read this file

# Path to package.json file
packageJson="$PWD/package.json"

# Read version code and name from package.json
appVersionCode=$(grep -o '"chark":\s*{[^}]*"versionCode":\s*[0-9]\+' "$packageJson" | awk -F':' '{print $3}' | tr -d '[:space:]')
appVersionName=$(grep -o '"version":\s*"[0-9]\+\.[0-9]\+\.[0-9]\+"' "$packageJson" | awk -F'"' '{print $4}')

# If version code is empty, read from "versionCode" at the top level
if [ -z "$appVersionCode" ]; then
    appVersionCode=$(grep -o '"versionCode":\s*[0-9]\+' "$packageJson" | awk -F':' '{print $2}' | tr -d '[:space:]')
fi

echo "Version code: $appVersionCode"
echo "Version name: $appVersionName"

# Path to  file
xcconfigFile="$PWD/ios/chark/Config.xcconfig"

# Write to the xcconfig file
echo "CURRENT_PROJECT_VERSION = $appVersionCode" > "$xcconfigFile"
echo "MARKETING_VERSION = $appVersionName" >> "$xcconfigFile"

echo "Updated $xcconfigFile: $xcconfigFile"
