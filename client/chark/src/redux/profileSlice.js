import { createSlice } from '@reduxjs/toolkit';

const initialState = {
  avatar: null,
  preferredCurrency: {
    code: '',
    name: '',
  },
  preferredLanguage: {
    name: '',
    code: '',
  },
  communications: [],
  personal: undefined,
  addresses: [],
  filter: {},
};

export const profileSlice = createSlice({
  name: 'profile',
  initialState: initialState,
  reducers: {
    setAvatar: (state, action) => {
      state.avatar = action.payload;
    },
    setPreferredCurrency: (state, action) => {
      state.preferredCurrency = action.payload;
    },
    setPreferredLanguage: (state, action) => {
      state.preferredLanguage = action.payload;
    },
    setCommunications: (state, action) => {
      state.communications = action.payload;
    },
    setAddress: (state, action) => {
      state.address = action.payload;
    },
    setPersonal: (state, action) => {
      state.personal = action.payload;
    },
    setFilter: (state, action) => {
    },
  },
});

export const {
  setAvatar,
  setPreferredCurrency,
  setPreferredLanguage,
  setCommunications,
  setAddress,
  setPersonal,
  setFilter,
} = profileSlice.actions;

export default profileSlice.reducer;
