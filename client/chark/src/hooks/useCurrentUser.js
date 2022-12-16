import { useContext } from 'react';

import UserContext from '../context/UserContext';

export default function() {
  const userContext = useContext(UserContext);

  return userContext;
}

