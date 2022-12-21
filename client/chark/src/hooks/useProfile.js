import { useContext } from 'react';

import ProfileContext from '../context/ProfileContext';

export default function() {
  const profileContext = useContext(ProfileContext);

  return profileContext;
}

