import { createSlice } from '@reduxjs/toolkit';

const initialState = {
  sortAscending: false,
  statusFilter: {
    values: ['good'],
    whereClause: "status = 'good'"
  },
  typeFilter: {
    values: ['lift', 'tran'],
    whereClause: "chit_type IN ('lift','tran')"
  }
};

export const chitHistoryFilterSlice = createSlice({
  name: 'chitHistoryFilter',
  initialState,
  reducers: {
    setSortDirection: (state, action) => {
      state.sortAscending = action.payload;
    },
    setStatusFilter: (state, action) => {
      state.statusFilter = action.payload;
    },
    setTypeFilter: (state, action) => {
      state.typeFilter = action.payload;
    }
  }
});

export const { setSortDirection, setStatusFilter, setTypeFilter } = chitHistoryFilterSlice.actions;
export default chitHistoryFilterSlice.reducer;