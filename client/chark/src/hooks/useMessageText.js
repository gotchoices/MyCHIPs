import { useContext } from 'react';

import MessageTextContext from '../context/MessageTextContext';

export default function() {
  const messageTextContext = useContext(MessageTextContext);

  return messageTextContext;
}

