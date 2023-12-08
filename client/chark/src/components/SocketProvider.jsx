import React, { useState, useEffect, useRef, useMemo } from 'react';
import * as Keychain from 'react-native-keychain';
import notifee, { AndroidImportance } from '@notifee/react-native'
import { Linking } from 'react-native'
import { useDispatch } from 'react-redux';

const wm = require('../wyseman')
import Connect, { headers } from '../connect';
import SocketContext from '../context/SocketContext';
import { query_user } from '../utils/user';
import { random, getLinkHost } from '../utils/common';
import { setUser } from '../redux/currentUserSlice';

const initialConnectionBackoff = 1000;
const maxConnectionBackoff = 11000;
const listenId = `listen_${random()}`;
const connectionUri = new Set(['connect', 'mychips.org/connect'])

const SocketProvider = ({ children }) => {
  const [ws, setWs] = useState();
  const [status, setStatus] = useState('Disconnected');
  const [tallyNegotiation, setTallyNegotiation] = useState(undefined);
  const [chitTrigger, setChitTrigger] = useState(undefined);
  const dispatch = useDispatch();

  const connectTimeout = useRef();
  const connectionBackoffRef = useRef(initialConnectionBackoff); // for exponential backoff 

  useEffect(() => {
    if(!ws) {
      Linking.getInitialURL().then((url) => {
        const host = getLinkHost(url ?? '');
        if(!connectionUri.has(host)) {
          connectSocket()
        }
      });
    }
  }, []);

  const credConnect = (creds, cb = null) => {
    const user = `mu_${creds.user}`;
    let address = `${creds.host}:${creds.port}`

    const connect = new Connect({
      webcrypto: window.crypto,
      listen: [user],
      wm,
    })

    setStatus('Connecting');

    connect.getUrl(creds).then(uri => {
      console.log('Connect:', uri)
      const websocket = new WebSocket(uri, '', { headers });

      websocket.onclose = () => {
        console.log('Socket connection closed')
        setStatus('Disconnected');
        setWs(null);
        wm.onClose()

        if(connectionBackoffRef.current < maxConnectionBackoff) {
          connectionBackoffRef.current *= 2;
        }

        const delay = connectionBackoffRef.current + Math.floor(Math.random() * 3500)
        connectTimeout.current = setTimeout(() => {
          connectSocket()
        }, delay)
      }

      websocket.onopen = () => {
        connectionBackoffRef.current = initialConnectionBackoff;
        setStatus('Connected');
        clearTimeout(connectTimeout.current);
        setWs(websocket);
        wm.listen(`${listenId}-${user}`, user, data => {
          console.log('notification data', data, 'NOTIFICATION DATA')
          onDisplayNotification(data);
          const payload = notificationTriggerPayload(data);
          if(data?.target === 'tally') {
            setTallyNegotiation(payload);
          } else if(data?.target === 'chit') {
            setChitTrigger(payload);
          }
        })

        wm.onOpen(address, m => {
          websocket.send(m)
        })

        // Query user and set it on the global context
        query_user(wm).then((data) => {
          dispatch(setUser(data?.[0]));
        })

        if(cb) {
          cb(null, true);
        }
      }

      websocket.onerror = err => {
        console.log('Websocket error', err)
        setStatus('Disconnected');
        wm.onClose()

        if(cb) {
          cb(err);
        }
      }

      websocket.onmessage = e => {
        wm.onMessage(e.data)
      }
    }).catch(err => {
      if(connectionBackoffRef.current < maxConnectionBackoff) {
        connectionBackoffRef.current *= 2;
      }
      const delay = connectionBackoffRef.current + Math.floor(Math.random() * 3500)
      console.log('Error initializing', err)
      setStatus('Disconnected');
      connectTimeout.current = setTimeout(() => {
        connectSocket()
      }, delay)

      if(cb) {
        cb(err);
      }
    })
  }

  const connectSocket = (connectionObj, cb = null) => {
    if (connectionObj) {
      clearTimeout(connectTimeout.current);
      console.log('Resetting generic password for the new connection')
      Keychain.resetGenericPassword();
      let creds = Object.assign({}, connectionObj.ticket)
      credConnect(creds, cb)
    } else {
      Keychain.getGenericPassword().then((credentials) => {
        if(credentials) {
          const val = credentials.password;
          const creds = JSON.parse(val);

          credConnect(creds);
        } 
      }).catch(err => {
        console.log('Error fetching connection key', err.message)
      });
    }
  }

  const disconnectSocket = () => {
    if(ws) {
      ws.close();
      setWs(null);
    }
  }

  return (
    <SocketContext.Provider value={{
      ws,
      wm,
      status,
      connectSocket,
      disconnectSocket,
      tallyNegotiation,
      chitTrigger,
    }}>
      {children}
    </SocketContext.Provider>
  )
}

async function onDisplayNotification(data) {
  // Request permissions (required for iOS)
  await notifee.requestPermission()
  
  // Create a channel (required for Android)
  const channelId = await notifee.createChannel({
    id: 'important',
    name: 'Default Channel',
    importance: AndroidImportance.HIGH,
  });

  const { title, message } = getTitleAndMessage({
    target: data.target,
    state: data.state,
    reason: data.reason,
  })

  // Display a notification
  await notifee.displayNotification({
    title: title,
    body: message ?? '',
    data: {
      type: 'tally-preview',
      tally_seq: data.sequence?.toString(),
      link: `mychips://tally-preview/${data.sequence}`,
    },
    android: {
      channelId,
      importance: AndroidImportance.HIGH,
      pressAction: {
        id: 'default',
      },
    },
  });
}

/**
  * @param {Object} args - Notification data
  * @param {string} args.reason - Argument obj
  * @param {string} args.target - Argument obj
  * @param {string} args.state - Argument obj
  */
function getTitleAndMessage(args) {
  const state_reason_Map = {
    'P.draft_valid': {
      title: 'Receive subject ticket',
      message: 'Subject has scanned and added a valid certificate',
    },
    'H.offer_offer': {
      title: 'Tally offered',
      message: 'You have offered a tally',
    },
    'P.offer_offer': {
      title: 'Tally offered',
      message: 'You have been offered a tally',
    },
    'P.draft_draft': {
      title: 'Tally revised',
      message: 'Tally has been revised',
    },
    'H.offer_draft': {
      title: 'Tally revised',
      message: 'Tally has been revised',
    },
    'open_open': {
      title: 'Tally opened',
      message: 'Tally has been opened',
    },
  };

  const tally_key = `${args.state}_${args.reason}`

  switch(args.target) {
    case 'tally':
      return {
        title: state_reason_Map[tally_key]?.title ?? 'Notification',
        message: state_reason_Map[tally_key]?.message ?? ''
      }

    default: 
      return {
        title: 'Notification',
        message: 'You have got a notification',
      }
  }
}

function notificationTriggerPayload(data) {
  switch(data?.target) {
      case 'tally':
        return {
          uuid: data?.object?.uuid,
          sequence: data?.sequence,
          state: data?.state,
          reason: data?.reason,
          entity: data?.entity,
        }

      case 'chit':
        return {
          tally_ent: data.entity,
          tally_seq: data.sequence,
          tally_uuid: data.object?.tally,
          hash: data.object?.hash,
          net: data?.net,
          pend: data?.pend,
        }

      default:
        break;
  }
}

export default SocketProvider;
