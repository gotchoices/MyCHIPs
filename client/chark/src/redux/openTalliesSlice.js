import { createSlice, createAsyncThunk } from '@reduxjs/toolkit';

import { fetchTallies } from '../services/tally';

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
      fields: ['tally_seq', 'tally_ent', 'net', 'tally_type', 'part_chad', 'part_cert'],
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
    throw err;
  }
})

export const openTalliesSlice = createSlice({
  name: 'openTallies',
  initialState: initialState,
  reducers: {
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
