import React, { useState, useEffect } from 'react';

import ProfileContext, { LangContext } from '../context/ProfileContext';
import useCurrentUser from '../hooks/useCurrentUser';
import { getComm, getPersonal, getAddresses, getLang } from '../services/profile';

const ProfileProvider = ({ wm, children }) => {
  const { user } = useCurrentUser();
  const user_ent = user?.curr_eid;

  const [communications, setCommunications] = useState([]);
  const [personal, setPersonal] = useState({});
  const [addresses, setAddresses] = useState([]);
  const [lang, setLang] = useState({});

  useEffect(() => {
    getComm(wm, user_ent).then(data => {
      setCommunications(data);
    })

    getPersonal(wm, user_ent).then(data => {
      setPersonal(data);
    })

    getAddresses(wm, user_ent).then(data => {
      setAddresses(data);
    })

    getLang(wm).then(data => {
      setLang(data);
    })
  }, [])

  return (
    <ProfileContext.Provider value={{
      lang,
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
