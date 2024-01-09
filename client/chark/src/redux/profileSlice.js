import { NativeModules } from 'react-native';
import { createSlice, createAsyncThunk } from '@reduxjs/toolkit';
import AsyncStorage from '@react-native-async-storage/async-storage'

import { languageMap } from '../utils/language';
import { getFile, uploadImage, getComm, getAddresses, getPersonal, getCurrency, getCountry } from '../services/profile';

const initialState = {
  loadingAvatar: false,
  avatar: undefined,
  preferredCurrency: {
    code: '',
    name: '',
  },
  preferredLanguage: {
    name: '',
    code: '',
  },
  communications: [],
  personal: undefined,
  addresses: [],
  filter: {},
  filterTally:{},
  // For detecting any change on user to trigger asynchronous change that depend on the tally 
  userChangeTrigger: 1,
  // Displaying modal for creating a signature
  showCreateSignatureModal: false,
  publicKey: '',
  privateKey: '',
};

export const fetchAvatar = createAsyncThunk('profile/fetchAvatar', async (args) => {
  try {
    const data = await getFile(args.wm, args.user_ent);

    const file = data?.[0];

    if(file?.file_data64) {
      return `data:${file.file_fmt};base64,${file.file_data64}`
    }

    return;
  } catch(err) {
    throw err;
  }
})

export const getPreferredLanguage = createAsyncThunk('profile/getPreferredLanguage', async (wm) => {
  try {
    const data = await AsyncStorage.getItem('preferredLanguage')
    if (data) {
      const language = JSON.parse(data);
      wm.newLanguage(language.code)
      return {
        name: language?.eng_name,
        code: language?.code,
      }
    } else {
      const deviceLanguage =
        Platform.OS === 'ios'
        ? NativeModules.SettingsManager.settings.AppleLocale || NativeModules.SettingsManager.settings.AppleLanguages[0]
        : NativeModules.I18nManager.localeIdentifier;

      return {
        name: languageMap[deviceLanguage]?.name ?? '',
        code: languageMap[deviceLanguage]?.language,
      }
    }
  } catch(err) {
    throw er;
  }
})

export const fetchPersonalAndCurrency = createAsyncThunk('profile/fetchPersonalAndCountry', async (args) => {
  try {
    const personal = await getPersonal(args.wm, args.user_ent)
    let currency = initialState.preferredCurrency;

    const preferredCurrency = await AsyncStorage.getItem('preferredCurrency')
    if (preferredCurrency) {
      try {
        const _currency = JSON.parse(preferredCurrency);
        currency = {
          name: _currency?.cur_name,
          code: _currency?.cur_code,
        }
      } catch (err) {
        console.log("Error parsing currecy data", err)
      }
    } else {
      const country = personal.country;
      if(country) {
        const _country = await getCountry(args.wm, country);
        const _currency = await getCurrency(args.wm, _country.cur_code)
        if (_currency) {
          currency = {
            name: _currency.cur_name,
            code: _currency.cur_code,
          }
        }
      }
    }

    return {
      personal,
      currency,
    }
  } catch(err) {
    throw err;
  }
})

export const uploadAvatar = createAsyncThunk('profile/uploadAvatar', async (args) => {
  try {
    const response = await uploadImage(args.wm, args.payload)
    if(response?.file_data64) {
      return `data:${response.fmt};base64,${response.file_data64}`
    }
  } catch(err) {
    throw err;
  }
})

export const fetchComm = createAsyncThunk('profile/fetchComm', async (args) => {
  try {
    const comm = await getComm(args.wm, args.user_ent)
    return comm;
  } catch(err) {
    throw err;
  }
})

export const fetchAddresses = createAsyncThunk('profile/fetchAddresses', async (args) => {
  try {
    const data = await getAddresses(args.wm, args.user_ent)
    return data;
  } catch(err) {
    throw err;
  }
})

export const getFilter = createAsyncThunk('profile/getFilter', async () => {
  const data = await AsyncStorage.getItem("filterData")
  if (data) {
    let filter = {};
    try {
      filter = JSON.parse(data);
    } catch (err) {
      console.log(err.message)
    }

    return filter ?? {};
  } else {
    const filter = {
      offer: { title: "Offers", selected: true, status: 'offer' },
      draft: { title: "Drafts", selected: true, status: 'draft' },
      void: { title: "Voids", selected: true, status: 'void' },
    }

    await AsyncStorage.setItem("filterData", JSON.stringify(filter))
    return filter;
  }
})

export const getTallyListFilter = createAsyncThunk('profile/getTallyListFilter', async () => {
  const data = await AsyncStorage.getItem("filterTallyList")
  
  if (data) {
    let filterTally = {};

    try {
      filterTally = JSON.parse(data);
    } catch (err) {
      console.log(err.message)
    }

    return filterTally ?? {};
  } else {
    const filterTally = {
      recent: { title: "Most Recent activity", selected: true, status: 'recent' },
      ascending: { title: "Positive to Negative (assets to liabilities)", selected: false, status: 'ascending' },
      descending: { title: "Negative to Positive (liabilities to assets)", selected: false, status: 'descending' },
      absolute: { title: "Absolute value (highest to lowest)", selected: false, status: 'absolute' },
      alphabetical: { title: "Alphabetical", selected: false, status: 'alphabetical' },
    }

    await AsyncStorage.setItem("filterTallyList", JSON.stringify(filterTally))

    return filterTally;
  }
})

export const profileSlice = createSlice({
  name: 'profile',
  initialState: initialState,
  reducers: {
    setAvatar: (state, action) => {
      state.avatar = action.payload;
    },
    setPreferredCurrency: (state, action) => {
      state.preferredCurrency = action.payload;
    },
    setPreferredLanguage: (state, action) => {
      state.preferredLanguage = action.payload;
    },
    setCommunications: (state, action) => {
      state.communications = action.payload;
    },
    setAddress: (state, action) => {
      state.address = action.payload;
    },
    setPersonal: (state, action) => {
      state.personal = action.payload;
    },
    setFilter: (state, action) => {
      state.filter = action.payload;
    },
    setFilterTally: (state, action) => {
      state.filterTally = action.payload;
    },
    setUserChangeTrigger: (state, action) => {
      const trigger = state.userChangeTrigger ?? 1;
      state.userChangeTrigger = trigger + 1;
    },
    setShowCreateSignatureModal: (state, action) => {
      state.showCreateSignatureModal = action.payload;
    },
    setPublicKey: (state, action) => {
      state.publicKey = action.payload;
    },
    setPrivateKey: (state, action) => {
      state.privateKey = action.payload;
    },
  },
  extraReducers: (builder) => {
    builder
      .addCase(fetchAvatar.fulfilled, (state, action) => {
        state.avatar = action.payload;
      })
      .addCase(getPreferredLanguage.fulfilled, (state, action) => {
        state.preferredLanguage = action.payload;
      })
      .addCase(fetchPersonalAndCurrency.fulfilled, (state, action) => {
        state.personal = action.payload.personal;
        state.preferredCurrency = action.payload.currency;
      })
      .addCase(uploadAvatar.pending, (state, action) => {
        state.loadingAvatar = true;
      })
      .addCase(uploadAvatar.fulfilled, (state, action) => {
        if(action.payload) {
          state.loadingAvatar = false;
          state.avatar = action.payload;
        }
      })
      .addCase(uploadAvatar.rejected, (state, action) => {
        state.loadingAvatar = false;
      })
      .addCase(fetchComm.fulfilled, (state, action) => {
        state.communications = action.payload
      })
      .addCase(fetchAddresses.fulfilled, (state, action) => {
        state.addresses = action.payload
      })
      .addCase(getFilter.fulfilled, (state, action) => {
        state.filter = action.payload
      })
      .addCase(getTallyListFilter.fulfilled, (state, action) => {
        state.filterTally = action.payload
      })
  },
});

export const {
  setAvatar,
  setFilter,
  setAddress,
  setPersonal,
  setFilterTally,
  setCommunications,
  setPreferredCurrency,
  setPreferredLanguage,
  setUserChangeTrigger,
  setShowCreateSignatureModal,
  setPublicKey,
  setPrivateKey,
} = profileSlice.actions;

export default profileSlice.reducer;
