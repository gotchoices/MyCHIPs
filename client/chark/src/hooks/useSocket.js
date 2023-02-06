import { useContext } from 'react';

import SocketContext from '../context/SocketContext';

export default function() {
  const socketContext = useContext(SocketContext);

  return socketContext;
}

