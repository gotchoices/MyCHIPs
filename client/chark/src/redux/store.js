import { configureStore } from '@reduxjs/toolkit';

import talliesReducer from './tallySlice';
import profileReducer from './profileSlice';
import languageReducer from './languageSlice';
import currencyReducer from './currencySlice';
import currentUserReducer from './currentUserSlice';

export default configureStore({
  reducer: {
    profile: profileReducer,
    tallies: talliesReducer,
    language: languageReducer,
    currency: currencyReducer,
    currentUser: currentUserReducer,
  }
})
