import { createSlice, createAsyncThunk } from '@reduxjs/toolkit';

import { fetchChits } from '../services/chit';
import { fetchTallies } from '../services/tally';

const initialState = {
  fetchingTallies: false,
  fetchingChits: false,
  chits: [],
  tallies: [],
};

export const getTallies = createAsyncThunk('activity/getTallies', async (args) => {
  try {
    const fields = [
      'tally_ent', 'tally_seq', 'tally_uuid', 'tally_type', 
      'part_cert', 'json_core', 'state', 'crt_date',
    ];

    const data = await fetchTallies(args.wm, {
      fields,
      where: ['action true'],
    })

    return data;
  } catch(err) {
    console.log({ err })
    throw err;
  }
})

export const getChits = createAsyncThunk('activity/getChits', async (args) => {
  try {
    const fields = [
      'chit_ent','chit_seq', 'chit_idx', 'chit_uuid', 'net_pc', 'units', 
      'net', 'memo', 'reference', 'json_core', 'chit_date', 'state'
    ];

    const data = await fetchChits(args.wm, {
      fields,
      where: ['action true']
    })

    return data;
  } catch(err) {
    console.log({ err })
    throw err;
  }
})


export const activitySlice = createSlice({
  name: 'activity',
  initialState: initialState,
  reducers: {
  },

  extraReducers: (builder) => {
    builder
      .addCase(getTallies.pending, (state, action) => {
        state.fetchingTallies = true;
      })
      .addCase(getTallies.fulfilled, (state, action) => {
        state.tallies = action.payload;
        state.fetchingTallies = false;
      })
      .addCase(getTallies.rejected, (state, action) => {
        state.fetchingTallies = false;
      })
      .addCase(getChits.pending, (state, action) => {
        state.fetchingChits = true;
      })
      .addCase(getChits.fulfilled, (state, action) => {
        state.chits = action.payload;
        state.fetchingChits = false;
      })
      .addCase(getChits.rejected, (state, action) => {
        state.fetchingChits = false;
      })
  },
});

export default activitySlice.reducer;

