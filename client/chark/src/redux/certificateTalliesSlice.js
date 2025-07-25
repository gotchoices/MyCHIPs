import { createSlice, createAsyncThunk } from '@reduxjs/toolkit';
import { v4 as uuid } from 'uuid';

import { fetchTallies } from '../services/tally';
import { getUserCert } from '../services/user';

const initialState = {
  /** 
  * Initially true, as need to check if the user has draft tallies or not
  * If not we display the custom certification options
  */
  fetching: false, 
  fetchingSingle: false,
  certificate: undefined,
  fromStartToCertSelection: false,
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
  file: {
    byId: {},
    ids: [],
  },
};

export const createCertificateState = (cert) => {
  const places = cert?.place ?? [];
  const _birth = cert?.identity?.birth ?? {};
  const connects = cert?.connect ?? [];
  const _state = cert?.identity?.state ?? {};
  const files = cert?.file ?? [];

  let birth = {};
  let state = {};
  const place = { byId: {}, ids: [] };
  const connect = { byId: {}, ids: [] };
  const file = { byId: {}, ids: [] };

  places.forEach((pl, index)=> {
    const id = uuid();
    place.byId[id] = { selected: true, ...pl }
    place.ids.push(id);
  })

  connects.forEach((conn, index)=> {
    const id = uuid();
    connect.byId[id] = { selected: true, ...conn }
    connect.ids.push(id);
  })

  files.forEach((fl, index)=> {
    const id = uuid();
    file.byId[id] = { selected: true, ...fl}
    file.ids.push(id);
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
    file,
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
      const { place, birth, connect, state, file } = createCertificateState(certificate);

      return {
        certificate,
        place,
        birth,
        connect,
        state,
        file,
      }
    }

    return;
  } catch(err) {
    console.log('FETCH CERTIFICATE>>', err)
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
        file,
      } = createCertificateState(cert);

      state.place = place;
      state.birth = birth;
      state.state = _state;
      state.connect = connect;
      state.file = file;
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

    /** 
    * @param {string|number} action.id
    * @param {boolean} action.selected
    */
    setFile: (state, action) => {
      const { id, selected } = action.payload
      const data = state.file.byId[id]
      console.log(id, data, 'DATE:w')
      if(data) {
        state.file.byId[id].selected = selected;
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
    },

    /**
    * Fetching to true and fromStartToCertSelection to false
    * to check for the draft tallies and navigate to custom certificate directly
    */
    startRequest: (state, action) => {
      state.fetching = true;
      state.fromStartToCertSelection = false;
    },
  },
  extraReducers: (builder) => {
    builder
      .addCase(fetchTalliesForCertificates.pending, (state) => {
        state.fetching = true;
      })
      .addCase(fetchTalliesForCertificates.fulfilled, (state, action) => {
        state.tallies = action.payload;
        state.fetching = false;
        if(!action.payload.length) {
          state.fromStartToCertSelection = true;
        }
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
        state.file = action.payload?.file;
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
  setFile,
  startRequest,
} = certificateTalliesSlice.actions;
