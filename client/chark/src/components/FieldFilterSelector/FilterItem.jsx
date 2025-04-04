import React from 'react';
import { Text, StyleSheet, TouchableOpacity } from 'react-native';
import PropTypes from 'prop-types';
import { SelectedIcon, UnSelectedIcon } from '../SvgAssets/SvgAssets';
import { colors } from '../../config/constants';

/**
 * Component for displaying a filter option with a checkbox
 * Used within the FilterModal component
 */
const FilterItem = ({ option, isSelected, onToggle }) => {
  return (
    <TouchableOpacity 
      style={styles.container}
      onPress={onToggle}
    >
      <Text style={styles.optionText}>{option.title}</Text>
      {isSelected ? <SelectedIcon /> : <UnSelectedIcon />}
    </TouchableOpacity>
  );
};

FilterItem.propTypes = {
  option: PropTypes.shape({
    value: PropTypes.string.isRequired,
    title: PropTypes.string.isRequired
  }).isRequired,
  isSelected: PropTypes.bool.isRequired,
  onToggle: PropTypes.func.isRequired
};

const styles = StyleSheet.create({
  container: {
    flexDirection: 'row',
    justifyContent: 'space-between',
    alignItems: 'center',
    paddingVertical: 12,
    paddingHorizontal: 24,
  },
  optionText: {
    fontSize: 16,
    color: colors.black100,
    fontFamily: 'inter',
  },
});

export default FilterItem;