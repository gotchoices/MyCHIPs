#!/bin/bash

# Path to version.properties file
versionFile="$PWD/version.properties"

# Read version code and name from version.properties
appVersionCode=$(grep '^VERSION_CODE=' "$versionFile" | cut -d'=' -f2)
appVersionName=$(grep '^VERSION_NAME=' "$versionFile" | cut -d'=' -f2)

# Path to Info.plist file
infoPlist="$PWD/ios/chark/Info.plist"

# Update Info.plist with the new version information
/usr/libexec/PlistBuddy -c "Set :CFBundleVersion $appVersionCode" "$infoPlist"
/usr/libexec/PlistBuddy -c "Set :CFBundleShortVersionString $appVersionName" "$infoPlist"

# Print the appVersionName
echo "$appVersionName"