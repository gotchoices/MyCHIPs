import { createContext } from 'react';

const SocketContext = createContext({
  ws: undefined,
  wm: undefined,
  status: 'Server Disconnected',
  connectSocket: (ticket) => {
    console.log('Connect socket');
  },
  disconnectSocket: () => {
    console.log('Disconnect socket');
  },
});

export default SocketContext;
