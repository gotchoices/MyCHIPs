import { createSlice, createAsyncThunk } from '@reduxjs/toolkit';

import { fetchTallies } from '../services/tally';

const initialState = {
  fetching: false,
  tallies: [],
  hashes: [],
  imageFetchTrigger: 1,
  // For detecting any change on working tally to trigger asynchronous change that depend on the tally 
  certificateChangeTrigger: undefined,
  place: {
    byId: {},
    ids: [],
  },
  birth: {},
  state: {},
  connect: {
    byId: {},
    ids: [],
  },
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
      'json_core',
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
          isHolder: false,
        })
      }

      if(holdDigest) {
        hashes.push({
          digest: holdDigest,
          tally_seq,
          isHolder: true,
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
        json_core: el.json_core,
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
    setCertificateChangeTrigger: (state, action) => {
      const { tally_ent, tally_seq, hold_cert = undefined} = action.payload;
      const trigger = state.certificateChangeTrigger?.trigger ?? 1;

      const change = {
        tally_ent,
        tally_seq,
        trigger: trigger + 1,
      }

      if(hold_cert) {
        change.hold_cert = hold_cert;
      }

      state.certificateChangeTrigger = change;
    },

    setCertificate: (state, action) => {
      const {
        place = initialState.place,
        birth = initialState.birth ,
        state:_state = initialState.state,
        connect = initialState.connect,
      } = action.payload ?? {};

      state.place = place;
      state.birth = birth;
      state.state = _state;
      state.connect = connect;
    },

    /** 
    * @param {string|number} action.id
    * @param {boolean} action.selected
    */
    setPlace: (state, action) => {
      const { id, selected } = action.payload
      const data = state.place.byId[id]
      if(data) {
        state.place.byId[id].selected = selected;
      }
    },
    /** 
    * @param {boolean} action.selected
    */
    setBirth: (state, action) => {
      const data = state.birth;
      if(data) {
        state.birth.selected = action.payload.selected;
      }
    },
    /** 
    * @param {boolean} action.selected
    */
    setState: (state, action) => {
      const data = state.state;
      if(data) {
        state.state.selected = action.payload.selected;
      }
    },
    /** 
    * @param {string|number} action.id
    * @param {boolean} action.selected
    */
    setConnect: (state, action) => {
      const { id, selected } = action.payload;
      const data = state.connect.byId[id]
      if(data) {
        state.connect.byId[id].selected = selected;
      }
    },

    resetCertificate: (state) => {
      state.place = initialState.place;
      state.birth = initialState.birth;
      state.state= initialState.state;
      state.connect = initialState.connect;
    },

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
  setCertificateChangeTrigger,
  setCertificate,
  setPlace,
  setBirth,
  setState,
  setConnect,
  resetCertificate,
} = workingTalliesSlice.actions; 
