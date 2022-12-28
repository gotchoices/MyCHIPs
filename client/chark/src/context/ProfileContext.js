import { createContext } from 'react';

const ProfileContext = createContext({
  communications: [],
  personal: undefined,
  addresses: [],
  lang: {},
  setLang: (data) => {
    console.log('Set lang');
  },
  setCommunications: (data) => {
    console.log('Set communication');
  },
  setAddress: (data) => {
    console.log('Set address');
  },
  setPersonal: (data) => {
    console.log('Set personal bio');
  },
})

export default ProfileContext;
