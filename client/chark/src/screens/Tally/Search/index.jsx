import React from 'react';
import { View, StyleSheet, TextInput, TouchableWithoutFeedback } from 'react-native';
import PropTypes from 'prop-types'

import { FilterIcon, SearchIcon } from '../../../components/SvgAssets/SvgAssets';
import { colors } from '../../../config/constants';
import useMessageText from '../../../hooks/useMessageText';

const Search = (props) => {

  const { messageText } = useMessageText();
  const charkText = messageText?.chark?.msg;

  return (
    <View style={styles.container}>
      <View style={styles.search}>
        <SearchIcon />
        <TextInput
          style={styles.searchInput}
          placeholder={charkText?.search?.title ?? ''}
          onChangeText={(text)=>props.searchInput(text)}
        />
      </View>
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

Search.propTypes = {
  title: PropTypes.string,
}

export default Search;
