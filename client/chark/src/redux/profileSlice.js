import { createSlice, createAsyncThunk } from '@reduxjs/toolkit';
import AsyncStorage from '@react-native-async-storage/async-storage'

import { getDeviceLocale, getAvailableLanguages, findMatchingLanguage } from '../utils/language';
import { getFile, uploadImage, getComm, getAddresses, getPersonal, getCurrency, getCountry } from '../services/profile';

const initialState = {
  loadingAvatar: false,
  avatar: undefined,
  preferredCurrency: {
    code: '',
    name: '',
  },
  preferredLanguage: {
    name: 'English',
    code: 'eng',
    iso_2: 'en'
  },
  communications: [],
  personal: undefined,
  addresses: [],
  filter: {},
  // filterTally removed - replaced by tallySortSlice
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
        iso_2: language?.iso_2
      }
    } else {
      // Use English as the default language
      return {
        name: 'English',
        code: 'eng',
        iso_2: 'en'
      };
    }
  } catch(err) {
    console.log('Error in getPreferredLanguage:', err);
    // Default to English in case of errors
    return {
      name: 'English',
      code: 'eng',
      iso_2: 'en'
    };
  }
})

export const detectAndSetLanguage = createAsyncThunk(
  'profile/detectAndSetLanguage',
  async (wm, { dispatch, getState }) => {
    try {
      // Step 1: Check if user has explicitly selected a language previously
      const storedPreference = await AsyncStorage.getItem('preferredLanguage');
      if (storedPreference) {
        const language = JSON.parse(storedPreference);
        // User already has a preference, no need to detect
        return null;
      }
      
      // Step 2: Get device locale
      const deviceLocale = getDeviceLocale();
      
      // Step 3: Get available languages
      const availableLanguages = await getAvailableLanguages(wm);
      
      // Step 4: Find matching language
      const matchedLanguage = findMatchingLanguage(deviceLocale, availableLanguages);
      
      if (matchedLanguage) {
        // Found a match to device locale, update language
        wm.newLanguage(matchedLanguage.code);
        
        // Save preference
        await AsyncStorage.setItem('preferredLanguage', JSON.stringify(matchedLanguage));
        
        return {
          name: matchedLanguage.eng_name,
          code: matchedLanguage.code,
          iso_2: matchedLanguage.iso_2
        };
      }
      
      // No match found, keep English default
      return null;
    } catch (error) {
      console.log('Error detecting language:', error);
      return null;
    }
  }
)

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
      offer: { selected: true, status: 'offer' },
      draft: { selected: true, status: 'draft' },
      void: { selected: true, status: 'void' },
    }

    await AsyncStorage.setItem("filterData", JSON.stringify(filter))
    return filter;
  }
})

// getTallyListFilter removed - replaced by tallySortSlice

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
    // setFilterTally removed - replaced by tallySortSlice
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
      .addCase(detectAndSetLanguage.fulfilled, (state, action) => {
        if (action.payload) {
          state.preferredLanguage = action.payload;
        }
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
      // getTallyListFilter.fulfilled case removed - replaced by tallySortSlice
  },
});

export const {
  setAvatar,
  setFilter,
  setAddress,
  setPersonal,
  // setFilterTally removed - replaced by tallySortSlice
  setCommunications,
  setPreferredCurrency,
  setPreferredLanguage,
  setUserChangeTrigger,
  setShowCreateSignatureModal,
  setPublicKey,
  setPrivateKey,
} = profileSlice.actions;

export default profileSlice.reducer;
