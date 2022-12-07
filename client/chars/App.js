import React from 'react';
import type {Node} from 'react';
import {
  LogBox,
  SafeAreaView,
  StatusBar,
  StyleSheet,
  View,
} from 'react-native';

import QRScan from './src/screens/QRScan.js';

LogBox.ignoreLogs([
    "ViewPropTypes will be removed",
    "ColorPropType will be removed",
    "componentWillMount has been renamed",
    `RNUILib's ChipsInput component will be deprecated soon, please use the "Incubator.ChipsInput" component instead`,
    'Warning: Each child in a list should have a unique "key" prop.'
])


const App: () => Node = () => {
  return (
    <SafeAreaView>
      <StatusBar barStyle={'dark-content'} />
      <QRScan />
    </SafeAreaView>
  );
};

export default App;
