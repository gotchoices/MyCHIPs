import { createSlice, createAsyncThunk } from '@reduxjs/toolkit';

import { getCurrency } from '../services/user';

const initialState = {
  fetching: false,
  currency: undefined,
  conversionRate: 0,
};

export const getCurrencyRate = createAsyncThunk('chipCurrency/getCurrencyRate', async (args, { getState }) => {
  try {
    const state = getState(); // <-- invoke and access state object
    const currentCurrencyCode = state.chipCurrency?.currency?.base;
    const preferredCurrencyCode = state.profile?.preferredCurrency?.code;

    let currency;
    if(currentCurrencyCode === preferredCurrencyCode) {
      currency = state.chipCurrency?.currency;
    } else {
      currency = await getCurrency(args.wm, args.currencyCode)
    }

    conversionRate = parseFloat(currency?.rate ?? 0)

    return {
      currency,
      conversionRate,
    };
  } catch(err) {
    console.log({ err })
    throw err;
  }
})


export const chipCurrencySlice = createSlice({
  name: 'chipCurrency',
  initialState: initialState,
  reducers: {
  },

  extraReducers: (builder) => {
    builder
      .addCase(getCurrencyRate.pending, (state) => {
        state.fetching = true;
      })
      .addCase(getCurrencyRate.fulfilled, (state, action) => {
        state.currency = action.payload.currency;
        state.conversionRate = action.payload.conversionRate;
        state.fetching = false;
      })
      .addCase(getCurrencyRate.rejected, (state) => {
        state.fetching = false;
      })
  },
});

export default chipCurrencySlice.reducer;

