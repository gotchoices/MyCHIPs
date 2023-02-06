import React, { useState, useEffect, useRef } from 'react';
import * as Keychain from 'react-native-keychain';

const wm = require('../wyseman')
import Connect, { headers } from '../connect';
import SocketContext from '../context/SocketContext';
import useCurrentUser from '../hooks/useCurrentUser';
import { query_user } from '../utils/user';

const listen = ['mychips_user','wylib']		//Listen for these notifies from the DB

const SocketProvider = ({ children }) => {
  const [ws, setWs] = useState();
  const [status, setStatus] = useState('Server Disconnected');

  const { setUser } = useCurrentUser();
  const connectTimeout = useRef();

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
    if(ws) return;

    setStatus('Connecting Server...');
    connect.getUrl(creds).then(uri => {
      console.log('Connect:', uri)
      const websocket = new WebSocket(uri, '', { headers });

      websocket.onclose = () => {
        console.log('Socket connection closed')
        setStatus('Server Disconnected');
        setWs(null);
        wm.onClose()

        connectTimeout.current = setTimeout(() => {
          connectSocket()
        }, 5000)
      }

      websocket.onopen = () => {
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
        setStatus('Server Disconnected');
        wm.onClose()

        if(err?.isTrusted === false) {
          Keychain.resetGenericPassword();
        }

        if(cb) {
          cb(err);
        }
      }

      websocket.onmessage = e => {
        wm.onMessage(e.data)
      }
    }).catch(err => {
      setStatus('Server Disconnected');
      connectTimeout.current = setTimeout(() => {
        connectSocket()
      }, 5000)

      if(cb) {
        cb(err);
      }
    })
  }

  const connectSocket = (ticket, cb = null) => {
    if (ticket) {
      clearTimeout(connectTimeout.current);
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
