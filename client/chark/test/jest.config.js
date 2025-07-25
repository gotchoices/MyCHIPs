/** @type {import('@jest/types').Config.InitialOptions} */
module.exports = {
  rootDir: '..',
  testMatch: ['<rootDir>/test/**/*.test.js'],
  testTimeout: 120000,
  maxWorkers: 1,
  globalSetup: 'detox/runners/jest/globalSetup',
  globalTeardown: 'detox/runners/jest/globalTeardown',
  reporters: ['detox/runners/jest/reporter'],
  testEnvironment: 'detox/runners/jest/testEnvironment',
  verbose: true,
  //setupFiles: ['<rootDir>/jest.setup.js'],
  transformIgnorePatterns: [
    'node_modules/(?!(jest-)?react-native|@react-native|@notifee)'
  ],
  //transformIgnorePatterns: [
    //"node_modules/(?!(react-native|react-native-.*|react-navigation|react-navigation-.*|@react-navigation)/)",
  //],
  //"globals": {
    //"__DEV__": true
  //},
  //transform: {
    //'^.+\\.[jt]sx?$': [
      //'babel-jest',
    //]
  //}
};
