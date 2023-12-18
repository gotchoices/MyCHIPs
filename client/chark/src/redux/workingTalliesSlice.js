import { createSlice, createAsyncThunk } from '@reduxjs/toolkit';

import { fetchTallies } from '../services/tally';

const initialState = {
  fetching: false,
  tallies: [],
  hashes: [],
  imageFetchTrigger: 1,
  // For detecting any change on working tally to trigger asynchronous change that depend on the tally 
  tallyChangeTrigger: undefined,
};

export const fetchTemplates = createAsyncThunk('workingTallies/fetchTemplates', async (args) => {
  try {
    const fields = [
      'tally_ent',
      'tally_seq',
      'contract',
      'comment',
      'tally_uuid',
      'hold_terms',
      'part_terms',
      'tally_type',
      'status',
      'part_cid',
      'part_cert',
      'hold_cert',
      'json',
      'state',
    ];

    const data = await fetchTallies(args.wm, {
      fields,
      where: { left: "status", oper: "in", entry: args.entry },
      order: {
        field: 'crt_date',
        asc: false,
      }
    })

    const hashes = []
    const tallies = data?.map(el => {
      const partDigest = el?.part_cert?.file?.[0]?.digest;
      const holdDigest = el?.hold_cert?.file?.[0]?.digest;
      const tally_seq = el?.tally_seq;

      if(partDigest) {
        hashes.push({
          digest: partDigest,
          tally_seq,
        })
      }

      if(holdDigest) {
        hashes.push({
          digest: holdDigest,
          tally_seq,
        })
      }

      return {
        tally_uuid: el.tally_uuid,
        tally_seq: el.tally_seq,
        tally_ent: el.tally_ent,
        id: el.tally_seq,
        contract: el.contract,
        comment: el.comment,
        hold_terms: el.hold_terms,
        part_terms: el.part_terms,
        tally_type: el.tally_type,
        status: el.status,
        part_cid: el.part_cid,
        part_cert: el.part_cert,
        hold_cert: el.hold_cert,
        state: el.state,
      }
    });

    return {
      tallies,
      hashes,
    }

  } catch(err) {
    throw err;
  }

})


export const workingTalliesSlice = createSlice({
  name: 'workingTallies',
  initialState: initialState,
  reducers: {
    updateTally: (state, action) => {
      const updated = action.payload;
      const foundIndex = state.tallies.findIndex(tally => (
        tally.tally_ent === updated.tally_ent && tally.tally_seq === updated.tally_seq
      ))

      if(foundIndex >= 0) {
        state.tallies[foundIndex] = updated;
      }
    },
    setTallyChangeTrigger: (state, action) => {
      const { tally_ent, tally_seq } = action.payload;
      const trigger = state.tallyChangeTrigger?.trigger ?? 1;

      state.tallyChangeTrigger = {
        tally_ent,
        tally_seq,
        trigger: trigger + 1,
      }
    }
  },

  extraReducers: (builder) => {
    builder
      .addCase(fetchTemplates.pending, (state, action) => {
        state.fetching = true;
      })
      .addCase(fetchTemplates.fulfilled, (state, action) => {
        state.tallies = action.payload.tallies;
        state.hashes = action.payload.hashes;
        state.imageFetchTrigger = state.imageFetchTrigger + 1;
        state.fetching = false;
      })
      .addCase(fetchTemplates.rejected, (state, action) => {
        state.fetching = false;
      })
  },
});

export default workingTalliesSlice.reducer;

export const {
  updateTally,
  setTallyChangeTrigger,
} = workingTalliesSlice.actions; 
