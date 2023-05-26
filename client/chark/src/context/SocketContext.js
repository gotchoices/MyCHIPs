import { createContext } from 'react';

const SocketContext = createContext({
  ws: undefined,
  wm: undefined,
  status: 'Server Disconnected',
  // used to trigger tally fetch in the tally review screen
  tallyState: undefined,
  connectSocket: (ticket) => {
    console.log('Connect socket');
  },
  disconnectSocket: () => {
    console.log('Disconnect socket');
  },
});

export default SocketContext;
