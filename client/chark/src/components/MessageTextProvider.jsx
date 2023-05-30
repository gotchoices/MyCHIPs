import React, { useState } from 'react';

import MessageTextContext from '../context/MessageTextContext';

const MessageTextProvider = ({ children }) => {
  const [messageText, setMessageText] = useState();

  return (
    <MessageTextContext.Provider value={{
      messageText,
      setMessageText,
    }}>
      {children}
    </MessageTextContext.Provider>
  )
}

export default MessageTextProvider;
