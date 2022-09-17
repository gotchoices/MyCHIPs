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
};
