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
      fields: ['tally_uuid', 'tally_seq', 'tally_ent', 'net', 'tally_type', 'part_chad', 'part_cert'],
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

/** 
  * Fetch tallies after the chit has been transferred
  * @param {Object} args
  * @param {any} args.wm
  * @param {string} args.tally_ent
  * @param {string|number} args.tally_seq
  * @param {string} args.tally_uuid
  */
export const fetchTallyOnChitTransferred = createAsyncThunk('openTallies/fetchTallyOnChitTransferred', async (args) => {
  try {
    const tallies = await fetchTallies(args.wm, {
      fields: ['tally_seq', 'tally_ent', 'net', 'tally_type', 'tally_uuid'],
      where: {
        status: 'open',
        tally_ent: args.tally_ent,
        tally_seq: args.tally_seq,
        tally_uuid: args.tally_uuid,
      }
    })

    if(tallies?.length > 1) {
      return
    }

    return tallies?.[0];

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
      .addCase(fetchTallyOnChitTransferred.pending, (state, action) => {
        state.fetching = true;
      })
      .addCase(fetchTallyOnChitTransferred.fulfilled, (state, action) => {
        const payload = action.payload;
        if(payload) {
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
            state.tallies[foundIndex] = {
              ...tally,
              ...(payload ?? {})
            }
          }
        }
        state.fetching = false;
      })
      .addCase(fetchTallyOnChitTransferred.rejected, (state, action) => {
        state.fetching = false;
      })
  },
});

export default openTalliesSlice.reducer;
