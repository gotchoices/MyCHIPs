import { createSlice, createAsyncThunk } from '@reduxjs/toolkit';

import { fetchChits } from '../services/chit';
import { fetchTallies } from '../services/tally';

const initialState = {
  fetchingTallies: true,
  fetchingChits: true,
  chits: [],
  goodChits: [],
  tallies: [],
  hasNotification: false,
};

export const hasNotification = createAsyncThunk('activity/checkNotification', async (args) => {
  try {
    const tallyFields = ['tally_ent'];
    const chitFields = ['chit_ent'];

    const tally = await fetchTallies(args.wm, {
      fields: tallyFields,
      where: ['action true'],
      limit: 1
    })

    const chit = await fetchChits(args.wm, {
      fields: chitFields,
      where: ['action true'],
      limit: 1,
    })

    if(tally?.length || chit?.length) {
      return true;
    }

    return false;
  } catch(err) {
    return false;
  }
})

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

export const getGoodChits = createAsyncThunk('activity/getGoodChits', async (args) => {
  try {
    const fields = [
      'chit_ent','chit_seq', 'chit_idx', 'chit_uuid', 'net_pc', 'units', 
      'net', 'memo', 'reference', 'json_core', 'chit_date', 'state', 'part_cid',
    ];

    const data = await fetchChits(args.wm, {
      fields,
      where: {
        left: 'state', oper: 'in', entry: ['A.good', 'L.good'],
      }
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
    setHasNotification: (state, action) => {
      state.hasNotification = action.payload;
    },
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
      .addCase(hasNotification.fulfilled, (state, action) => {
        state.hasNotification = action.payload;
      })
      .addCase(getGoodChits.fulfilled, (state, action) => {
        state.goodChits = action.payload;
      })
  },
});

export default activitySlice.reducer;

export const {
  setHasNotification,
} = activitySlice.actions;

