/**
 * Metro configuration
 * https://reactnative.dev/docs/metro
 *
 * @type {import('@react-native/metro-config').MetroConfig}
*/
const {getDefaultConfig, mergeConfig} = require('@react-native/metro-config');

// Add SVG transformer support
const config = {
  transformer: {
    babelTransformerPath: require.resolve("react-native-svg-transformer"),
  },
  resolver: {
    assetExts: ['png', 'jpg', 'jpeg', 'gif', 'webp'],
    sourceExts: ['js', 'jsx', 'json', 'ts', 'tsx', 'svg'],
  }
};

module.exports = mergeConfig(getDefaultConfig(__dirname), config);