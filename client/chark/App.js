// MyCHIPs Mobile Application
// Copyright MyCHIPs.org
// TODO:
//- Connection:
//X-  Wrap websocket module
//X-  Can we do without origin in wsoptions?
//X-  entcli still works
//- 

import React, { useEffect, useRef } from 'react';
import { SafeAreaView } from 'react-native';
import { NavigationContainer, getStateFromPath, DefaultTheme } from '@react-navigation/native';
import PolyfillCrypto from 'react-native-webview-crypto'
import Toast from 'react-native-toast-message';
import notifee from '@notifee/react-native';
import qs from 'query-string';
import { Provider } from 'react-redux';
import { PersistGate } from 'redux-persist/integration/react'

import ServIcon from './src/servicon'
import SocketProvider from './src/components/SocketProvider';
import MessageTextProvider from './src/components/MessageTextProvider';
import Navigator from './src/navigation/Navigator';

import { handleNotification } from './src/utils/notification';

import store, { persistor } from './src/redux/store';

const linking = {
  prefixes: ["mychips://", "https://mychips.org"],
  getStateFromPath: (path, options) => {
    const parsed = qs.parseUrl(path);
    //const newPath = parsed.url === '/invite' ? '/ticket' : path;
    let newPath;
    if(['/invite', '/pay'].includes(parsed.url)) {
      newPath = '/ticket';
    } else {
      newPath = '/ticket';
    }

    return getStateFromPath(newPath, options);
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

              <PolyfillCrypto />

              <Navigator />
            </MessageTextProvider>

            <Toast />
          </SocketProvider>
        </NavigationContainer>
      </SafeAreaView>
      </PersistGate>
    </Provider>
  );
}

export default App;

