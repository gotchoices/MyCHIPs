#!/bin/bash

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

# Path to Info.plist file
infoPlist="$PWD/ios/chark/Info.plist"

# Update Info.plist with the new version information
/usr/libexec/PlistBuddy -c "Set :CFBundleVersion $appVersionCode" "$infoPlist"
/usr/libexec/PlistBuddy -c "Set :CFBundleShortVersionString $appVersionName" "$infoPlist"

# Print the appVersionName
echo "Updated Info.plist with version code: $appVersionCode and version name: $appVersionName"
