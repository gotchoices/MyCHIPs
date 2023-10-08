import React from 'react';
import { View, StyleSheet, TextInput, TouchableWithoutFeedback } from 'react-native';

import { FilterIcon, SearchIcon } from '../../../components/SvgAssets/SvgAssets';
import { colors } from '../../../config/constants';

const Search = () => {
  const onFilter = () => {
    console.log('filter pressed')
  }

  return (
    <View style={styles.container}>
      <View style={styles.search}>
        <SearchIcon />
        <TextInput
          style={styles.searchInput}
          placeholder="Search Partners"
        />
      </View>

      <TouchableWithoutFeedback onPress={onFilter}>
        <View style={styles.filter}>
          <FilterIcon />
        </View>
      </TouchableWithoutFeedback>
    </View>
  )
}

const styles = StyleSheet.create({
  container: {
    flexDirection: 'row',
    alignItems: 'center',
    justifyContent: 'space-between',
    borderRadius:5,
    borderWidth: 1,
    borderColor:colors.lightgray
  },
  search: {
    paddingHorizontal: 16,
    // backgroundColor: '#f2f4f7',
    width: '85%',
    flexDirection: 'row',
    alignItems: 'center',
    borderRadius: 8,
  },
  searchInput: {
    padding: 10,
  },
  filter: {
    padding: 10
  }
});


export default Search;
