import React, { useState } from 'react';

import MessageTextContext from '../context/MessageTextContext';

const initialTexts = {
  tallies: null,
  comm: null,
  addr_v_flat: null,
  addr_v: null,
  users: null,
  exchange: null,
  userTallies: null,
  asset_v: null,
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
