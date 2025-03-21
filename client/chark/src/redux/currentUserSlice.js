import { createSlice } from '@reduxjs/toolkit';
const initialState = {
  user: undefined,
} 

export const userSlice = createSlice({
  name: 'currentUser',
  initialState: initialState,
  reducers: {
    setUser: (state, action) => {
      state.user = action.payload;
    }
  },
});

export const { setUser } = userSlice.actions;

export default userSlice.reducer;
