import {createSlice} from '@reduxjs/toolkit';

/**
 * Redux slice for managing home screen tally list sorting
 * - Maintains the active sorter and individual sort states
 * - Preserves sort preferences across app sessions
 * 
 * Sort directions:
 * - "asc": Ascending (A-Z, oldest first, smallest first)
 * - "desc": Descending (Z-A, newest first, largest first)
 * - "abs": Absolute value (for balance sort only)
 */
const initialState = {
  // Currently active sorter
  activeSorter: 'date',
  
  // Name sorter state
  nameSort: {
    direction: 'asc',
    field: 'part_cert',
  },
  
  // Date sorter state
  dateSort: {
    direction: 'desc', // Default - newest first
    field: 'tally_date',
  },
  
  // Balance sorter state
  balanceSort: {
    direction: 'desc', // Default - largest first
    field: 'net',
  }
};

export const tallySortSlice = createSlice({
  name: 'tallySort',
  initialState,
  reducers: {
    // Set the active sorter (name, date, balance)
    setActiveSorter: (state, action) => {
      state.activeSorter = action.payload;
    },
    
    // Toggle name sort direction (asc/desc)
    toggleNameSort: (state) => {
      // Toggle between asc/desc
      state.nameSort.direction = state.nameSort.direction === 'asc' ? 'desc' : 'asc';
      // Set as active sorter
      state.activeSorter = 'name';
    },
    
    // Toggle date sort direction (asc/desc)
    toggleDateSort: (state) => {
      // Toggle between asc/desc
      state.dateSort.direction = state.dateSort.direction === 'asc' ? 'desc' : 'asc';
      // Set as active sorter
      state.activeSorter = 'date';
    },
    
    // Toggle balance sort direction (asc/desc/abs)
    toggleBalanceSort: (state) => {
      // Cycle through asc -> desc -> abs -> asc
      if (state.balanceSort.direction === 'asc') {
        state.balanceSort.direction = 'desc';
      } else if (state.balanceSort.direction === 'desc') {
        state.balanceSort.direction = 'abs';
      } else {
        state.balanceSort.direction = 'asc';
      }
      // Set as active sorter
      state.activeSorter = 'balance';
    },
    
    // Reset to default sort (date, newest first)
    resetSort: (state) => {
      return initialState;
    }
  },
});

// Export actions
export const {
  setActiveSorter,
  toggleNameSort,
  toggleDateSort,
  toggleBalanceSort,
  resetSort,
} = tallySortSlice.actions;

// Export selectors
export const selectActiveSorter = (state) => state.tallySort.activeSorter;
export const selectNameSort = (state) => state.tallySort.nameSort;
export const selectDateSort = (state) => state.tallySort.dateSort;
export const selectBalanceSort = (state) => state.tallySort.balanceSort;

// Export the current sort configuration based on active sorter
export const selectCurrentSort = (state) => {
  const {activeSorter, nameSort, dateSort, balanceSort} = state.tallySort;
  
  switch (activeSorter) {
    case 'name':
      return nameSort;
    case 'date':
      return dateSort;
    case 'balance':
      return balanceSort;
    default:
      return dateSort; // Default to date sort
  }
};

export default tallySortSlice.reducer;