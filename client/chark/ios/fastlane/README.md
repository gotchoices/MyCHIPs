fastlane documentation
----

# Installation

Make sure you have the latest version of the Xcode command line tools installed:

```sh
xcode-select --install
```

For _fastlane_ installation instructions, see [Installing _fastlane_](https://docs.fastlane.tools/#installing-fastlane)

# Available Actions

## iOS

### ios test_api_key

```sh
[bundle exec] fastlane ios test_api_key
```

Test App Store Connect API key configuration

### ios build_archive

```sh
[bundle exec] fastlane ios build_archive
```

Build the iOS app archive

### ios beta

```sh
[bundle exec] fastlane ios beta
```

Build and deploy to TestFlight

### ios release

```sh
[bundle exec] fastlane ios release
```

Build and deploy to App Store

### ios upload_only

```sh
[bundle exec] fastlane ios upload_only
```

Upload to TestFlight without rebuilding

----

This README.md is auto-generated and will be re-generated every time [_fastlane_](https://fastlane.tools) is run.

More information about _fastlane_ can be found on [fastlane.tools](https://fastlane.tools).

The documentation of _fastlane_ can be found on [docs.fastlane.tools](https://docs.fastlane.tools).
