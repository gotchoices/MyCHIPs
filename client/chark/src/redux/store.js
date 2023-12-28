import { configureStore } from '@reduxjs/toolkit';

import workingTalliesReducer from './workingTalliesSlice';
import profileReducer from './profileSlice';
import languageReducer from './languageSlice';
import currentUserReducer from './currentUserSlice';
import openTalliesReducer from './openTalliesSlice';
import avatarReducer from './avatarSlice';
import certificateTalliesReducer  from './certificateTalliesSlice';
import chitsReducer  from './chitSlice';
import chipCurrencyReducer  from './chipCurrencySlice';

export default configureStore({
  middleware: (getDefaultMiddleware) => getDefaultMiddleware({
    immutableCheck: false,
    serializableCheck: false,
  }),
  reducer: {
    profile: profileReducer,
    workingTallies: workingTalliesReducer,
    language: languageReducer,
    currentUser: currentUserReducer,
    openTallies: openTalliesReducer,
    avatar: avatarReducer,
    certificateTallies: certificateTalliesReducer,
    chit: chitsReducer,
    chipCurrency: chipCurrencyReducer,
  },
})
