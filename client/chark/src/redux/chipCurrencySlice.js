import { createSlice, createAsyncThunk } from '@reduxjs/toolkit';

import { getCurrency } from '../services/user';

const initialState = {
  fetching: false,
  currency: undefined,
  conversionRate: 0,
  error: null,
};

/**
 * Fetch the current conversion rate for CHIPs to the preferred currency
 * 
 * This thunk will get the conversion rate for the user's preferred currency
 * and update the Redux store.
 * 
 * @param {Object} args - Arguments object
 * @param {Object} args.wm - Wyseman client instance
 * @param {string} args.currencyCode - ISO currency code (e.g., 'USD', 'EUR')
 * @returns {Object} - Object containing currency info and conversionRate
 */
export const getCurrencyRate = createAsyncThunk(
  'chipCurrency/getCurrencyRate', 
  async (args, { getState, rejectWithValue }) => {
    try {
      if (!args.wm || !args.currencyCode) {
        console.log('Missing required parameters for getCurrencyRate:', args);
        return rejectWithValue('Missing required parameters: wm or currencyCode');
      }
      
      console.log('Fetching currency rate for:', args.currencyCode);
      
      // Get the currency rate from the backend
      const currency = await getCurrency(args.wm, args.currencyCode);
      
      // Parse the conversion rate
      const conversionRate = parseFloat(currency?.rate ?? 0);
      
      console.log('Fetched conversion rate:', conversionRate);
      
      return {
        currency,
        conversionRate,
      };
    } catch(err) {
      console.error('Error fetching currency rate:', err);
      return rejectWithValue(err.message || 'Unknown error fetching currency rate');
    }
  }
)


export const chipCurrencySlice = createSlice({
  name: 'chipCurrency',
  initialState: initialState,
  reducers: {
    resetCurrencyState: (state) => {
      state.fetching = false;
      state.error = null;
    }
  },

  extraReducers: (builder) => {
    builder
      .addCase(getCurrencyRate.pending, (state) => {
        state.fetching = true;
        state.error = null;
      })
      .addCase(getCurrencyRate.fulfilled, (state, action) => {
        state.currency = action.payload.currency;
        state.conversionRate = action.payload.conversionRate;
        state.fetching = false;
        state.error = null;
      })
      .addCase(getCurrencyRate.rejected, (state, action) => {
        state.fetching = false;
        state.error = action.payload || 'Failed to fetch currency rate';
        console.error('Currency rate fetch failed:', state.error);
      })
  },
});

export const { resetCurrencyState } = chipCurrencySlice.actions;

export default chipCurrencySlice.reducer;

