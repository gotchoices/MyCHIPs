import { createSlice, createAsyncThunk } from '@reduxjs/toolkit';
import { getTallyValidityStatus } from '../utils/tally-verification';

/**
 * This slice is responsible for updating a tally's data when it changes,
 * such as after a chit is transferred or a tally's validity status changes.
 * 
 * It ensures that:
 * 1. Components can update Redux with new tally information
 * 2. These updates trigger proper reactivity in the UI
 * 3. Non-fetch updates can be properly processed
 */

const initialState = {
  updating: false,
  tally: null,
  validityStatuses: {}, // Map of tally_uuid to validity status
};

// Async thunk for updating a tally's validity status
export const updateValidity = createAsyncThunk(
  'updateTally/updateValidity',
  async (tallyData) => {
    try {
      const validityStatus = await getTallyValidityStatus(tallyData);
      
      return {
        tallyUuid: tallyData.tally_uuid,
        tallyEnt: tallyData.tally_ent,
        tallySeq: tallyData.tally_seq,
        validityStatus
      };
    } catch (error) {
      console.error('Error updating tally validity:', error);
      throw error;
    }
  }
);

export const updateTallySlice = createSlice({
  name: 'updateTally',
  initialState,
  reducers: {
    setValidityStatus: (state, action) => {
      const { tallyUuid, validityStatus } = action.payload;
      
      if (tallyUuid) {
        state.validityStatuses[tallyUuid] = validityStatus;
      }
    },
    
    clearValidityStatuses: (state) => {
      state.validityStatuses = {};
    }
  },
  extraReducers: (builder) => {
    builder
      .addCase(updateValidity.pending, (state) => {
        state.updating = true;
      })
      .addCase(updateValidity.fulfilled, (state, action) => {
        const { tallyUuid, validityStatus } = action.payload;
        
        if (tallyUuid) {
          state.validityStatuses[tallyUuid] = validityStatus;
        }
        
        state.updating = false;
      })
      .addCase(updateValidity.rejected, (state) => {
        state.updating = false;
      });
  },
});

export const { 
  setValidityStatus,
  clearValidityStatuses
} = updateTallySlice.actions;

export default updateTallySlice.reducer;