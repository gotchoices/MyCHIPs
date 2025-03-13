/**
 * Metro configuration
 * https://reactnative.dev/docs/metro
 *
 * @type {import('@react-native/metro-config').MetroConfig}
*/
const {getDefaultConfig, mergeConfig} = require('@react-native/metro-config');

// Determine if we're in development mode
const isDev = process.env.NODE_ENV !== 'production';

// Add SVG transformer support
const config = {
  transformer: {
    babelTransformerPath: require.resolve("react-native-svg-transformer"),
    
    // Enable detailed source maps in development mode
    ...(isDev ? {
      minifierConfig: {
        keep_classnames: true,
        keep_fnames: true,
        mangle: {
          keep_classnames: true,
          keep_fnames: true
        }
      },
      enableBabelRuntime: true
    } : {})
  },
  resolver: {
    assetExts: ['png', 'jpg', 'jpeg', 'gif', 'webp'],
    sourceExts: ['js', 'jsx', 'json', 'ts', 'tsx', 'svg'],
  }
};

module.exports = mergeConfig(getDefaultConfig(__dirname), config);