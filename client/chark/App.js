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
import { NavigationContainer, getStateFromPath } from '@react-navigation/native';
import PolyfillCrypto from 'react-native-webview-crypto'
import Toast from 'react-native-toast-message';
import notifee from '@notifee/react-native';
import qs from 'query-string';
import { Provider } from 'react-redux';

import ServIcon from './src/servicon'
import SocketProvider from './src/components/SocketProvider';
import MessageTextProvider from './src/components/MessageTextProvider';
import Navigator from './src/navigation/Navigator';

import { handleNotification } from './src/utils/notification';

import store from './src/redux/store';

const linking = {
  prefixes: ["mychips://", "https://mychips.org"],
  getStateFromPath: (path, options) => {
    const parsed = qs.parseUrl(path);
    const newPath = parsed.url === '/tally' ? '/connect' : path;
    return getStateFromPath(newPath, options);
  },
  config: {
    screens: {
      Tally: {
        screens: {
          Home: {
            path: 'connect',
          },
          TallyPreview: {
            path: 'tally-preview/:tally_seq',
          },
        }
      },
    },
  },
};

function App() {
  const navigationRef = useRef();

  useEffect(() => {
    return notifee.onForegroundEvent(event => {
      console.log(event, 'event')
      handleNotification({
        ...event,
        navigationRef,
      });
    });
  }, []);

  return (
    <Provider store={store}>
      <SafeAreaView style={{ flex: 1 }}>
        <NavigationContainer linking={linking} ref={navigationRef}>
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
    </Provider>
  );
}

export default App;

