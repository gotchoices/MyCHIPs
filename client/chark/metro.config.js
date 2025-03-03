/**
 * Metro configuration
 * https://reactnative.dev/docs/metro
 *
 * @type {import('@react-native/metro-config').MetroConfig}
*/
const {getDefaultConfig, mergeConfig} = require('@react-native/metro-config');
const config = {};
module.exports = mergeConfig(getDefaultConfig(__dirname), config);

//Older versions below:

//For running out of local wyseman source package:
//const path = require('path')
//const wysemanPath = path.resolve(__dirname, '/../../../wyseman/')
//const watchFolders = [wysemanPath]
//const nodeModulesPaths = [wysemanPath]

/* 
const { getDefaultConfig } = require("metro-config");

module.exports = (async () => {
  const {
    resolver: { sourceExts, assetExts }
  } = await getDefaultConfig();
  return {
    transformer: {
      babelTransformerPath: require.resolve("react-native-svg-transformer"),
      getTransformOptions: async () => ({
        transform: {
          experimentalImportSupport: false,
          inlineRequires: true,
        },
      }),
    },
    resolver: {
      assetExts: assetExts.filter(ext => ext !== "svg"),
      sourceExts: [...sourceExts, "svg"]
    }
  };
})();
*/
/* 
module.exports = {
//  resolver: {nodeModulesPaths},
//  watchFolders,
  
  transformer: {
    getTransformOptions: async () => ({
      transform: {
        experimentalImportSupport: false,
        inlineRequires: true,
      },
    }),
  },
}; */
