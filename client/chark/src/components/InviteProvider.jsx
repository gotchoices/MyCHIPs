import React, { useState } from 'react';

import InviteContext from '../context/InviteContext';

const InviteProvider = ({ children }) => {
  const [triggerInviteFetch, setTriggerInviteFetch] = useState(1);

  return (
    <InviteContext.Provider value={{
      triggerInviteFetch,
      setTriggerInviteFetch,
    }}>
      {children}
    </InviteContext.Provider>
  )
}

export default InviteProvider;
