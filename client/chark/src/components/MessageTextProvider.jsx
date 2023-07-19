import React, { useState } from 'react';

import MessageTextContext from '../context/MessageTextContext';

const initialTexts = {
  tallies: {},
  comm: {},
  addr_v_flat: {},
  addr_v: {},
  users: {},
  exchange: {},
}

const MessageTextProvider = ({ children }) => {
  const [messageText, setMessageText] = useState(initialTexts);

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
