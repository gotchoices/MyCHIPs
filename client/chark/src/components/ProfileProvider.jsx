import React, { useState, useEffect } from 'react';

import ProfileContext from '../context/ProfileContext';
import useCurrentUser from '../hooks/useCurrentUser';
import { getComm, getPersonal, getAddresses, getLang } from '../services/profile';

const ProfileProvider = ({ children }) => {
  const { user } = useCurrentUser();
  const user_ent = user?.curr_eid;

  const [communications, setCommunications] = useState([]);
  const [personal, setPersonal] = useState({});
  const [addresses, setAddresses] = useState([]);
  const [lang, setLang] = useState({});

  return (
    <ProfileContext.Provider value={{
      lang,
      setLang,
      communications,
      addresses,
      personal,
      setCommunications,
      setPersonal,
      setAddresses,
    }}>
      {children}
    </ProfileContext.Provider>
  )
}

export default ProfileProvider;
