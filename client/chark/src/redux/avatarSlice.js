import { Buffer } from 'buffer';
import { createSlice, createAsyncThunk } from '@reduxjs/toolkit';
import AsyncStorage from '@react-native-async-storage/async-storage'

import { localStorage } from '../config/constants';
import { fetchTallyFile, getHolderImage } from '../services/tally';

const initialState = {
  imagesByDigest: {}, // { [digest]: string }
};

/**
  * @param {Object} - args
  * @param {tally} - args.tally
  */
export const fetchImagesByDigest = createAsyncThunk('avatar/fetchImagesByDigest', async (args, { getState }) => {
  const state = getState();
  const imagesByDigestState = state.avatar?.imagesByDigest ?? {};
  let hashes = [];

  if(args.status === 'open') {
    const tallies = state.openTallies;
    hashes = tallies.hashes ?? [];
  } else if(args.status === 'working') {
    const tallies = state.workingTallies;
    hashes = tallies.hashes ?? [];
  } else if(args.status === 'activity') {
    const activity = state.activity;
    hashes = activity.hashes ?? [];
  }

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

    if(hash.isHolder) {
      promises.push(getHolderImage(args.wm, hash.digest));
    } else {
      promises.push(fetchTallyFile(args.wm, hash.digest, hash.tally_seq));
    }
  }

  try {
    const files = await Promise.all(promises);

    for(let file of files) {
      const fileData = file?.[0]?.file_data ?? file?.[0]?.file_data64;
      const fileData64 = file?.[0]?.file_data64;
      const file_fmt = file?.[0]?.file_fmt;
      const digest = file?.[0]?.digest;

      if(fileData64) {
        const image = `data:${file_fmt};base64,${fileData64}`;
        _imagesByDigest[digest] = image;
      } else if(fileData) {
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

export const avatarSlice = createSlice({
  name: 'avatar',
  initialState: initialState,
  reducers: {
  },
  extraReducers: (builder) => {
    builder
      .addCase(fetchImagesByDigest.fulfilled, (state, action) => {
        state.imagesByDigest = action.payload ?? {};
      })
  },
});

export default avatarSlice.reducer;
