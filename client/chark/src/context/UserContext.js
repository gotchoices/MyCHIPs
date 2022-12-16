import { createContext } from 'react';

const UserContext = createContext({
  user: undefined,
  setUser: (user) => {
    console.log('Set user');
  }
})

export default UserContext;
