import { EventType } from '@notifee/react-native';

export const handleNotification = ({
  navigationRef,
  ...event
}) => {
  const { type, detail } = event;

  switch (type) {
    case EventType.DISMISSED:
      console.log('User dismissed notification', detail.notification);
      break;

    case EventType.PRESS:
      const data = detail.notification?.data ?? {};
      navigationRef.current?.navigate?.('TallyPreview', { ...data })
      break;

    default:
      break;
  }

}
