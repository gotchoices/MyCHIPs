import { configureStore } from '@reduxjs/toolkit';

import workingTalliesReducer from './workingTalliesSlice';
import profileReducer from './profileSlice';
import languageReducer from './languageSlice';
import currentUserReducer from './currentUserSlice';

export default configureStore({
  reducer: {
    profile: profileReducer,
    workingTallies: workingTalliesReducer,
    language: languageReducer,
    currentUser: currentUserReducer,
  }
})
