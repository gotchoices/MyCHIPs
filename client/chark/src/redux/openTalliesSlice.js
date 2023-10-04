import { Buffer } from 'buffer';
import { createSlice, createAsyncThunk } from '@reduxjs/toolkit';
import AsyncStorage from '@react-native-async-storage/async-storage'

import { localStorage } from '../config/constants';
import { fetchTallies, fetchTallyFile } from '../services/tally';

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

export const fetchImagesByDigest = createAsyncThunk('openTallies/fetchImagesByDigest', async (args, { getState }) => {
  const state = getState();
  const openTallies = state.openTallies;
  const hashes = openTallies.hashes ?? [];
  const imagesByDigestState = openTallies?.imagesByDigest ?? {};

  const promises = [];

  let _imagesByDigest = {};
  try {
    const storageValue = await AsyncStorage.getItem(localStorage.TallyPictures);
    _imagesByDigest = JSON.parse(storageValue ?? {});
  } catch(err) {
    _imagesByDigest = {};
  }

  for(let hash of hashes) {
    if(hash.digest in _imagesByDigest || imagesByDigestState[hash.digest]) {
      continue;
    }

    promises.push(fetchTallyFile(args.wm, hash.digest, hash.tally_seq));
  }

  try {
    const files = await Promise.all(promises);

    for(let file of files) {
      const fileData = file?.[0]?.file_data;
      const file_fmt = file?.[0]?.file_fmt;
      const digest = file?.[0]?.digest;

      if(fileData) {
        const base64 = Buffer.from(fileData).toString('base64')
        const image = `data:${file_fmt};base64,${base64}`;
        _imagesByDigest[digest] = image;
      }
    }

    await AsyncStorage.setItem(localStorage.TallyPictures, JSON.stringify(_imagesByDigest));

    return {
      ...imagesByDigestState,
      ..._imagesByDigest,
    }
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
      .addCase(fetchImagesByDigest.fulfilled, (state, action) => {
        state.imagesByDigest = action.payload ?? {};
      })
  },
});

export default openTalliesSlice.reducer;
