import React from 'react';
import { View, StyleSheet, Image, TextInput, TouchableWithoutFeedback } from 'react-native';

import searchImg from '../../../../assets/search.png';
import filterImg from '../../../../assets/filter.png';

const Search = () => {
  const onFilter = () => {
    console.log('filter pressed')
  }

  return (
    <View style={styles.container}>
      <View style={styles.search}>
        <Image source={searchImg} style={{ width: 20, height: 20}} />
        <TextInput 
          style={styles.searchInput}
          placeholder="Search Partners"
        />
      </View>

      <TouchableWithoutFeedback onPress={onFilter}>
        <View style={styles.filter}>
          <Image
            source={filterImg}
          />
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
  },
  search: {
    paddingHorizontal: 16,
    backgroundColor: '#f2f4f7',
    width: '85%',
    flexDirection: 'row',
    alignItems: 'center',
    borderRadius: 8,
  },
  searchInput: {
    paddingHorizontal: 10,
  },
  filter: {
    padding: 10
  }
});


export default Search;
