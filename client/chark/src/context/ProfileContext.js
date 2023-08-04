import { createContext } from 'react';

const ProfileContext = createContext({
  avatar: null,
  setAvatar: (av) => {
    console.log(av)
  },
  preferredCurrency: {
    code: '',
    name: '',
  },
  setPreferredCurrency: (data) => {
    console.log(data)
  },
  preferredLanguage: {
    name: '',
    code: '',
  },
  setPreferredLanguage: (_) => {
    console.log('set preferred language')
  },
  communications: [],
  personal: undefined,
  addresses: [],
  setCommunications: (_) => {
    console.log('Set communication');
  },
  setAddress: (_) => {
    console.log('Set address');
  },
  setPersonal: (_) => {
    console.log('Set personal bio');
  },
  filter: {},
  setFilter: (_) => {
    console.log('Set Filter');
  }
})

export default ProfileContext;
