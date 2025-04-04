// MyCHIPs Mobile Application
// Copyright MyCHIPs.org

import React, { useEffect, useRef } from 'react';
import { SafeAreaView } from 'react-native';
import { NavigationContainer, getStateFromPath, DefaultTheme } from '@react-navigation/native';
import QuickCrypto from 'react-native-quick-crypto';
import { Buffer } from '@craftzdog/react-native-buffer';
import notifee from '@notifee/react-native';

// Initialize crypto service (which handles Buffer and QuickCrypto initialization)
import { initCryptoService } from './src/services/crypto';
initCryptoService();
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
  prefixes: ["https://mychips.org"],
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
          OpenTallyEdit: {
            path: 'tally-view/:tally_seq',
          },
        }
      },
      Settings: {
        screens: {
          KeyManagement: {
            path: 'signkey',
          },
        }
      },
      Home: {
        // Tally invitation links are first routed to Home screen,
        // which then navigates to the appropriate TallyRequest screen
        path: 'invite',
      },
      PaymentDetail: {
        // Payment links go directly to the PaymentDetail screen
        path: 'pay',
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
