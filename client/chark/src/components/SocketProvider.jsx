import React, { useState, useEffect, useRef } from 'react';
import * as Keychain from 'react-native-keychain';

const wm = require('../wyseman')
import Connect, { headers } from '../connect';
import SocketContext from '../context/SocketContext';
import useCurrentUser from '../hooks/useCurrentUser';
import { query_user } from '../utils/user';

const listen = ['mychips_user','wylib']		//Listen for these notifies from the DB

const initialConnectionBackoff = 1000;
const maxConnectionBackoff = 11000;

const SocketProvider = ({ children }) => {
  const [ws, setWs] = useState();
  const [status, setStatus] = useState('Server Disconnected');

  const { setUser } = useCurrentUser();
  const connectTimeout = useRef();
  const connectionBackoffRef = useRef(initialConnectionBackoff); // for exponential backoff 

  useEffect(() => {
    if(!ws) {
      connectSocket()
    }
  }, []);


  const connect = new Connect({
    webcrypto: window.crypto,
    listen: listen,
    wm,
  })

  const credConnect = (creds, cb = null) => {
    let address = `${creds.host}:${creds.port}`

    setStatus('Connecting Server...');
    connect.getUrl(creds).then(uri => {
      console.log('Connect:', uri)
      const websocket = new WebSocket(uri, '', { headers });

      websocket.onclose = () => {
        console.log('Socket connection closed')
        setStatus('Server Disconnected');
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
        setStatus('Server Connected');
        clearTimeout(connectTimeout.current);
        setWs(websocket);
        wm.onOpen(address, m => {
          websocket.send(m)
        })

        // Query user and set it on the global context
        query_user(wm).then((data) => {
          setUser(data?.[0]);
        })

        if(cb) {
          cb(null, true);
        }
      }

      websocket.onerror = err => {
        console.log('Websocket error', err)
        setStatus('Server Disconnected');
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
      setStatus('Server Disconnected');
      connectTimeout.current = setTimeout(() => {
        connectSocket()
      }, delay)

      if(cb) {
        cb(err);
      }
    })
  }

  const connectSocket = (ticket, cb = null) => {
    if(ws) {
      if(!cb) return;

      const err = new Error('User already connected');
      return cb(err);
    };

    if (ticket) {
      clearTimeout(connectTimeout.current);
      console.log('Resetting generic password for the new connection')
      Keychain.resetGenericPassword();
      let creds = Object.assign({}, ticket.ticket)
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
    }}>
      {children}
    </SocketContext.Provider>
  )
}

export default SocketProvider;
