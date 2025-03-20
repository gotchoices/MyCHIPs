// MyCHIPs Mobile Application
// Copyright MyCHIPs.org

import React, { useEffect, useRef } from 'react';
import { SafeAreaView } from 'react-native';
import { NavigationContainer, getStateFromPath, DefaultTheme } from '@react-navigation/native';
import QuickCrypto from 'react-native-quick-crypto';
import { Buffer } from '@craftzdog/react-native-buffer';
import notifee from '@notifee/react-native';

// Initialize Buffer and QuickCrypto globals
global.Buffer = Buffer;
QuickCrypto.install();
import qs from 'query-string';
import { Provider } from 'react-redux';
import { PersistGate } from 'redux-persist/integration/react'
import ServIcon from './src/servicon'
import SocketProvider from './src/components/SocketProvider';
import MessageTextProvider from './src/components/MessageTextProvider';
import Navigator from './src/navigation/Navigator';
import CustomToast from './src/components/Toast';
import { handleNotification } from './src/utils/notification';
import store, { persistor } from './src/redux/store';

const linking = {
  prefixes: ["mychips://", "https://mychips.org"],
  getStateFromPath: (path, options) => {
    return getStateFromPath(path, options);
  },
  config: {
    screens: {
      Tally: {
        screens: {
          Home: {
            path: 'ticket',
          },
          TallyPreview: {
            path: 'tally-preview/:tally_seq',
          },
        }
      },
    },
  },
};

const theme = {
  ...DefaultTheme,
  colors: {
    ...DefaultTheme.colors,
    background:'white'
  },
};

function App() {
  const navigationRef = useRef();
  

  useEffect(() => {
    return notifee.onForegroundEvent(event => {
      handleNotification({
        ...event,
        navigationRef,
      });
    });
  }, []);

  return (
    <Provider store={store}>
      <PersistGate loading={null} persistor={persistor}>

      <SafeAreaView style={{ flex: 1 }}>
        <NavigationContainer linking={linking} ref={navigationRef} theme={theme}>
          <SocketProvider>
            <MessageTextProvider>
              <ServIcon />

              <Navigator />
            </MessageTextProvider>

            <CustomToast />
          </SocketProvider>
        </NavigationContainer>
      </SafeAreaView>
      </PersistGate>
    </Provider>
  );
}

export default App;
