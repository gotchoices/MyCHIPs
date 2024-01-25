import { createSlice, createAsyncThunk } from '@reduxjs/toolkit';

import { fetchTallies } from '../services/tally';
import { isNil } from '../utils/common';

const initialState = {
  fetching: false,
  tallies: [],
  hashes: [],
  imagesByDigest: {}, // { [digest]: string }
  imageFetchTrigger: 1,
};

export const fetchOpenTallies = createAsyncThunk('openTallies/fetchOpenTallies', async (args) => {
  try {
    const tallies = await fetchTallies(args.wm, {
      fields: ['tally_uuid', 'tally_seq', 'tally_ent', 'net','mag_p','tally_date', 'tally_type', 'part_chad', 'part_cert', 'hold_chad', 'net_pc'],
      where: {
        status: 'open',
      }
    })

    const hashes = [];
    for(let tally of tallies) {
      const digest = tally?.part_cert?.file?.[0]?.digest;
      const tally_seq = tally?.tally_seq;

      if(digest) {
        hashes.push({
          digest,
          tally_seq,
        })
      }
    }

    return {
      tallies,
      hashes,
    };
  } catch(err) {
    console.log({ err })
    throw err;
  }
})

export const openTalliesSlice = createSlice({
  name: 'openTallies',
  initialState: initialState,
  reducers: {
    updateTallyOnChitTransferred: (state, action) => {
      const payload = action.payload;
      if(payload && !isNil(payload.net)) {
        const tallies = state.tallies;
        const foundIndex = tallies.findIndex((tally) => {
          return (
            tally.tally_uuid === payload.tally_uuid && 
            tally.tally_ent === payload.tally_ent &&
            tally.tally_seq == payload.tally_seq
          )
        });

        if(foundIndex >= 0) {
          const tally = state.tallies[foundIndex];
          const update = {
            ...tally,
            net: payload.net,
          }
          if(payload.pend) {
            update.net_pc = payload.pend;
          }

          state.tallies[foundIndex] = update;
        }
      }
      state.fetching = false;
    }
  },

  extraReducers: (builder) => {
    builder
      .addCase(fetchOpenTallies.pending, (state, action) => {
        state.fetching = true;
      })
      .addCase(fetchOpenTallies.fulfilled, (state, action) => {
        state.tallies = action.payload.tallies;
        state.hashes = action.payload.hashes;
        state.imageFetchTrigger = state.imageFetchTrigger + 1;
        state.fetching = false;
      })
      .addCase(fetchOpenTallies.rejected, (state, action) => {
        state.fetching = false;
      })
  },
});

export default openTalliesSlice.reducer;

export const {
  updateTallyOnChitTransferred,
} = openTalliesSlice.actions;
