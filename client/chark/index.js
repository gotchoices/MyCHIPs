/**
 * @format
 */

import { AppRegistry, Linking } from 'react-native';
import App from './App';
import {name as appName} from './app.json';
import 'react-native-reanimated'
import notifee, { EventType } from '@notifee/react-native';

notifee.onBackgroundEvent(async ({ type, detail }) => {
  const { notification } = detail;

  switch(type) {
    case EventType.ACTION_PRESS:
      await notifee.cancelNotification(notification.id);
      break;
    case EventType.PRESS:
      console.log('press notification', notification?.data);
      Linking.openURL(notification?.data?.link)
      break;
    default:
      break;
  }
});


AppRegistry.registerComponent(appName, () => App);
