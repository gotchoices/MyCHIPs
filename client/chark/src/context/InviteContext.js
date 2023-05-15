import { createContext } from 'react';

const InviteContext = createContext({
  triggerInviteFetch: 1,
  setTriggerInviteFetch: (count) => {
    console.log('Set trigger invite fetch')
  }
});

export default InviteContext;
