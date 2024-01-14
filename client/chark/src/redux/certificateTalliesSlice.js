import { createSlice, createAsyncThunk } from '@reduxjs/toolkit';

import { fetchTallies } from '../services/tally';
import { getUserCert } from '../services/user';

const initialState = {
  fetching: false,
  fetchingSingle: false,
  certificate: undefined,
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

export const createCertificateState = (cert) => {
  const places = cert?.place ?? [];
  const _birth = cert?.identity?.birth ?? {};
  const connects = cert?.connect ?? [];
  const _state = cert?.identity?.state ?? {};

  let birth = {};
  let state = {};
  const place = { byId: {}, ids: [] };
  const connect = { byId: {}, ids: [] };

  places.forEach((pl, index)=> {
    place.byId[index] = { selected: true, ...pl }
    place.ids.push(index);
  })

  connects.forEach((conn, index)=> {
    connect.byId[index] = { selected: true, ...conn }
    connect.ids.push(index);
  })

  if(_state) {
    state = {
      selected: true,
      data: _state,
    }
  }

  if(_birth) {
    birth = {
      selected: true,
      data: _birth
    }
  }

  return {
    place,
    birth,
    connect,
    state,
  }
}

const getTallyCert = async (args) => {
  const fields = [
    'hold_cert',
  ];

  const tallies = await fetchTallies(args.wm, {
    fields,
    where: {
      tally_ent: args.tally_ent,
      tally_seq: args.tally_seq,
    },
  })

  if(tallies?.length) {
    const tally = tallies[0];
    const certificate = tally?.hold_cert;
    return certificate;
  }
}

export const fetchTalliesForCertificates = createAsyncThunk('certificateTallies/tallies', async (args) => {
  try {
    const fields = [
      'tally_ent',
      'tally_seq',
      'comment',
      'crt_date',
    ];

    const tallies = await fetchTallies(args.wm, {
      fields,
      where: { left: 'state', oper: 'in', entry: ['draft'] },
      order: {
        field: 'crt_date',
        asc: false,
      }
    })
    return tallies;
  } catch(err) {
    throw err;
  }
})

/** 
  * @param {Object} args
  * @param {any} args.wm - Wyseman instance
  * @param {string} args.type ('user' | 'tally')
  * @param {string} [args.tally_ent]
  * @param {string} [args.tally_seq]
  */
export const fetchCertificate = createAsyncThunk('certificateTallies/fetchCertificate', async (args) => {
  try {
    let certificate;
    if(args.type === 'user') {
      certificate = await getUserCert(args.wm);
    } else if(args.type === 'tally') {
      certificate = await getTallyCert({
        wm: args.wm,
        tally_ent: args.tally_ent,
        tally_seq: args.tally_seq,
      });
    }

    if(certificate) {
      const { place, birth, connect, state } = createCertificateState(certificate);

      return {
        certificate,
        place,
        birth,
        connect,
        state
      }
    }

    return;
  } catch(err) {
    throw err;
  }
})

export const certificateTalliesSlice = createSlice({
  name: 'certificateTallies',
  initialState: initialState,
  reducers: {
    setCertificateState: (state, action) => {
      const cert = action.payload;
      const {
        place,
        birth,
        state:_state,
        connect,
      } = createCertificateState(cert);

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

    selectAllCert: (state, action) => {
      for(const key in state.place.byId) {
        state.place.byId[key].selected = true;
      }

      for(const key in state.connect.byId) {
        state.connect.byId[key].selected = true;
      }

      for(const key in state.state.byId) {
        state.state.byId[key].selected = true;
      }

      if('selected' in state.birth) {
        state.birth.selected = true;
      }
    }
  },
  extraReducers: (builder) => {
    builder
      .addCase(fetchTalliesForCertificates.pending, (state) => {
        state.fetching = true;
      })
      .addCase(fetchTalliesForCertificates.fulfilled, (state, action) => {
        state.tallies = action.payload;
        state.fetching = false;
      })
      .addCase(fetchTalliesForCertificates.rejected, (state) => {
        state.fetching = false;
      })
      .addCase(fetchCertificate.pending, (state) => {
        state.fetchingSingle = true;
      })
      .addCase(fetchCertificate.fulfilled, (state, action) => {
        state.certificate = action.payload?.certificate;
        state.place = action.payload?.place;
        state.birth = action.payload?.birth;
        state.state = action.payload?.state;
        state.connect = action.payload?.connect;
        state.fetchingSingle = false;
      })
      .addCase(fetchCertificate.rejected, (state) => {
        state.fetchingSingle = false;
      })
  },
});

export default certificateTalliesSlice.reducer;

export const {
  setCertificateState,
  setPlace,
  setBirth,
  setConnect,
  setState,
  selectAllCert,
} = certificateTalliesSlice.actions;
