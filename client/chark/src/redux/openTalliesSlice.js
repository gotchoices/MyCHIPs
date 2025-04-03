import { createSlice, createAsyncThunk } from '@reduxjs/toolkit';

import { fetchTallies } from '../services/tally';
import { isNil } from '../utils/common';
import { getTallyValidityStatus } from '../utils/tally-verification';

const initialState = {
  fetching: false,
  tallies: [],
  hashes: [],
  imageFetchTrigger: 1,
  /**
  * Contains partner digest by tally_uuid
  * Chits by default do not contain image(image digest) and chits fall under tallies
  * So, need to get the image of the chit from the tally
  */
  partnerDigestByTallies: {}, 
};

export const fetchOpenTallies = createAsyncThunk('openTallies/fetchOpenTallies', async (args, {dispatch}) => {
  try {
    // Include necessary fields for validation
    const tallies = await fetchTallies(args.wm, {
      fields: [
        'tally_uuid', 'tally_seq', 'tally_ent', 'net','mag_p','tally_date', 
        'tally_type', 'part_chad', 'part_cert', 'hold_chad', 'net_pc',
        'json_core', 'hold_sig', 'hold_cert' // Required for validation
      ],
      where: {
        status: 'open',
      }
    })

    const partnerDigestByTallies = {};
    const hashes = [];
    
    // First process all non-validation properties to return quickly
    for(let tally of tallies) {
      const digest = tally?.part_cert?.file?.[0]?.digest;
      const tally_seq = tally?.tally_seq;
      partnerDigestByTallies[tally.tally_uuid] = digest;

      if(digest) {
        hashes.push({
          digest,
          tally_seq,
        })
      }
      
      // Initialize validity status to undefined
      tally.validityStatus = undefined;
    }

    // Return immediately to update the UI with basic tally data
    const result = {
      tallies,
      hashes,
      partnerDigestByTallies,
    };
    
    // Then process validation asynchronously in the background
    // and dispatch updates when each tally is validated
    Promise.all(tallies.map(async (tally) => {
      try {
        const status = await getTallyValidityStatus(tally);
        return {
          tallyUuid: tally.tally_uuid,
          tallyEnt: tally.tally_ent,
          tallySeq: tally.tally_seq,
          validityStatus: status
        };
      } catch (err) {
        console.error(`Error validating tally #${tally.tally_seq}:`, err);
        return {
          tallyUuid: tally.tally_uuid,
          tallyEnt: tally.tally_ent,
          tallySeq: tally.tally_seq,
          validityStatus: 'invalid'
        };
      }
    })).then(validationResults => {
      // Update both our openTallies slice and the updateTally slice
      dispatch(updateTallyValidityStatuses(validationResults));
      
      // Also update the dedicated updateTally slice
      validationResults.forEach(result => {
        if (result.tallyUuid) {
          import('./updateTallySlice').then(module => {
            dispatch(module.setValidityStatus({
              tallyUuid: result.tallyUuid,
              validityStatus: result.validityStatus
            }));
          });
        }
      });
    });

    return result;
  } catch(err) {
    console.log('FETCH OPEN TALLIES>>>', { err })
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
    },
    
    // New action to update tally validity statuses
    updateTallyValidityStatuses: (state, action) => {
      const validationResults = action.payload;
      
      if (!validationResults || !Array.isArray(validationResults)) {
        return;
      }
      
      // Update each tally with its validation result
      validationResults.forEach(result => {
        const { tallyUuid, tallyEnt, tallySeq, validityStatus } = result;
        
        // Find the tally in the state
        const foundIndex = state.tallies.findIndex(tally => {
          return (
            tally.tally_uuid === tallyUuid && 
            tally.tally_ent === tallyEnt &&
            tally.tally_seq == tallySeq
          );
        });
        
        // Update the tally if found
        if (foundIndex >= 0) {
          state.tallies[foundIndex] = {
            ...state.tallies[foundIndex],
            validityStatus
          };
        }
      });
    },
    
    // Action to update a single tally's validity status
    updateTallyValidityStatus: (state, action) => {
      const { tallyUuid, tallyEnt, tallySeq, validityStatus } = action.payload;
      
      // Find the tally in the state
      const foundIndex = state.tallies.findIndex(tally => {
        return (
          tally.tally_uuid === tallyUuid && 
          tally.tally_ent === tallyEnt &&
          tally.tally_seq == tallySeq
        );
      });
      
      // Update the tally if found
      if (foundIndex >= 0) {
        state.tallies[foundIndex] = {
          ...state.tallies[foundIndex],
          validityStatus
        };
      }
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
        state.partnerDigestByTallies = action.payload.partnerDigestByTallies;
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
  updateTallyValidityStatuses,
  updateTallyValidityStatus
} = openTalliesSlice.actions;
