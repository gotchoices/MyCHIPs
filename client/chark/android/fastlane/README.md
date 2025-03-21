fastlane documentation
----

# Installation

Make sure you have the latest version of the Xcode command line tools installed:

```sh
xcode-select --install
```

For _fastlane_ installation instructions, see [Installing _fastlane_](https://docs.fastlane.tools/#installing-fastlane)

# Available Actions

## Android

### android build_apk

```sh
[bundle exec] fastlane android build_apk
```

Build release APK

### android build_app_bundle

```sh
[bundle exec] fastlane android build_app_bundle
```

Build app bundle for Play Store submission

### android deploy_to_mychips

```sh
[bundle exec] fastlane android deploy_to_mychips
```

Deploy APK to mychips.org

### android deploy_to_playstore_testing

```sh
[bundle exec] fastlane android deploy_to_playstore_testing
```

Deploy app bundle to Play Store open testing track

### android deploy_to_playstore

```sh
[bundle exec] fastlane android deploy_to_playstore
```

Deploy app bundle to Play Store production

----

This README.md is auto-generated and will be re-generated every time [_fastlane_](https://fastlane.tools) is run.

More information about _fastlane_ can be found on [fastlane.tools](https://fastlane.tools).

The documentation of _fastlane_ can be found on [docs.fastlane.tools](https://docs.fastlane.tools).
