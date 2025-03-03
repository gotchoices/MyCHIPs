module.exports = {
  presets: ['module:@react-native/babel-preset'],
    
  plugins: [
    [
      'react-native-reanimated/plugin',
      {
        globals: ['__scanCodes'],
      },
    ]
  ],
};

