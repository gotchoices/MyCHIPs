import { createSlice, createAsyncThunk } from '@reduxjs/toolkit';

import { fetchChits } from '../services/chit';

const initialState = {
  fetching: false,
  chits: [],
};

export const getChits = createAsyncThunk('chits/getChits', async (args) => {
  try {
    const fields = ['chit_ent','chit_seq', 'chit_idx', 'chit_uuid', 'net_pc', 'units', 'net', 'memo', 'reference', 'json_core', 'chit_date', 'state', 'issuer', 'tally_type'];

    const data = await fetchChits(args.wm, {
      fields,
      where: {
        status: 'pend',
        tally_uuid: args.tally_uuid,
      }
    })

    return data;

  } catch(err) {
    console.log({ err })
    throw err;
  }
})


export const chitsSlice = createSlice({
  name: 'chits',
  initialState: initialState,
  reducers: {
    resetChits: (state, action) => {
      state.chits = [];
    }
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

export const {
  resetChits,
} = chitsSlice.actions;

