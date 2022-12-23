import { createContext } from 'react';

const ProfileContext = createContext({
  communications: [],
  personal: undefined,
  addresses: [],
  lang: {},
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

export const LangContext = createContext({
  lang: {},
  setLang: (data) => {
    console.log('Set lang');
  },
});


export default ProfileContext;
