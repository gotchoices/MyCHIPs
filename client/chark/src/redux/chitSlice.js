import { createSlice, createAsyncThunk } from '@reduxjs/toolkit';

import { fetchChits } from '../services/chit';

const initialState = {
  fetching: false,
  chits: [],
};

export const getChits = createAsyncThunk('chits/getChits', async (args) => {
  try {
    const fields = ['net_pc', 'units', 'net', 'memo'];

    const data = await fetchChits(args.wm, {
      fields,
      where: {
        status: 'pend'
      }
    })

    return data;

  } catch(err) {
    console.log({ err })
    throw err;
  }
})


export const chitsSlice = createSlice({
  name: 'workingTallies',
  initialState: initialState,
  reducers: {
  },

  extraReducers: (builder) => {
    builder
      .addCase(getChits.pending, (state, action) => {
        state.fetching = true;
      })
      .addCase(getChits.fulfilled, (state, action) => {
        state.chits = action.payload;
        state.fetching = false;
      })
      .addCase(getChits.rejected, (state, action) => {
        state.fetching = false;
      })
  },
});

export default chitsSlice.reducer;

