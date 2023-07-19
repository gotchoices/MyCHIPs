/**
 * Metro configuration for React Native
 * https://github.com/facebook/react-native
 *
 * @format
 */
//For running out of local wyseman source package:
//const path = require('path')
//const wysemanPath = path.resolve(__dirname, '/../../../wyseman/')
//const watchFolders = [wysemanPath]
//const nodeModulesPaths = [wysemanPath]


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
