import { useContext } from 'react';

import InviteContext from '../context/InviteContext';

export default function() {
  const inviteContext = useContext(InviteContext);

  return inviteContext;
}

