import { createContext } from 'react';

const MessageTextContext = createContext({
  messageText: {},
  setMessageText: (_) => {
    console.log('Set message text')
  },
})

export default MessageTextContext;
