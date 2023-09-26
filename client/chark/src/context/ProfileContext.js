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
  personal: undefined,
  setPersonal: (_) => {
    console.log('Set personal bio');
  },
  filter: {},
  setFilter: (_) => {
    console.log('Set Filter');
  }
})

export default ProfileContext;
