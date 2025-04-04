import React, { useState, useEffect, useMemo } from 'react';
import { TouchableOpacity, Text, StyleSheet } from 'react-native';
import PropTypes from 'prop-types';
import { FilterSecondIcon } from '../SvgAssets/SvgAssets';
import FilterModal from './FilterModal';
import { colors } from '../../config/constants';

/**
 * A reusable filter component that can be used to filter on any field
 * Displays a button that when pressed shows a modal with filter options
 * Supports multi-select and generates appropriate SQL WHERE clauses
 */
const FieldFilterSelector = ({
  fieldName,
  screenId,
  options,
  initialSelected = [],
  buttonLabel,
  onFilterChange,
  buttonStyle,
  buttonTextStyle,
}) => {
  const [modalVisible, setModalVisible] = useState(false);
  const [selectedValues, setSelectedValues] = useState(initialSelected);
  
  // Update selected values when initialSelected changes
  useEffect(() => {
    setSelectedValues(initialSelected);
  }, [JSON.stringify(initialSelected)]);
  
  // Generate WHERE clause based on selections
  const generateWhereClause = (selections) => {
    if (!selections || selections.length === 0) return '';
    
    // If all options are selected, don't filter
    if (selections.length === options.length) return '';
    
    // If only one option is selected
    if (selections.length === 1) return `${fieldName} = '${selections[0]}'`;
    
    // Multiple options selected
    return `${fieldName} IN ('${selections.join("','")}')`;
  };
  
  const handleFilterChange = (newSelections) => {
    setSelectedValues(newSelections);
    
    // Generate WHERE clause and call the callback
    const whereClause = generateWhereClause(newSelections);
    if (onFilterChange) {
      onFilterChange(newSelections, whereClause, fieldName);
    }
    
    setModalVisible(false);
  };
  
  // Get display text for button - using useMemo to ensure it updates correctly
  const buttonText = useMemo(() => {
    if (selectedValues.length === 0) {
      return buttonLabel || fieldName;
    }
    
    if (selectedValues.length === options.length) {
      return `${buttonLabel || fieldName}: *`;
    }
    
    return `${buttonLabel || fieldName} (${selectedValues.length})`;
  }, [selectedValues, options, buttonLabel, fieldName]);
  
  return (
    <>
      <TouchableOpacity 
        style={[styles.filterButton, buttonStyle]}
        onPress={() => setModalVisible(true)}
      >
        <FilterSecondIcon />
        <Text style={[styles.filterText, buttonTextStyle]}>
          {buttonText}
        </Text>
      </TouchableOpacity>
      
      <FilterModal
        visible={modalVisible}
        options={options}
        selectedValues={selectedValues}
        fieldName={fieldName}
        buttonLabel={buttonLabel}
        onClose={() => setModalVisible(false)}
        onSave={handleFilterChange}
      />
    </>
  );
};

FieldFilterSelector.propTypes = {
  fieldName: PropTypes.string.isRequired,
  screenId: PropTypes.string.isRequired,
  options: PropTypes.arrayOf(
    PropTypes.shape({
      value: PropTypes.string.isRequired,
      title: PropTypes.string.isRequired
    })
  ).isRequired,
  initialSelected: PropTypes.arrayOf(PropTypes.string),
  buttonLabel: PropTypes.string,
  onFilterChange: PropTypes.func,
  buttonStyle: PropTypes.object,
  buttonTextStyle: PropTypes.object
};

const styles = StyleSheet.create({
  filterButton: {
    borderWidth: 1,
    height: 30,
    borderColor: colors.white100,
    backgroundColor: colors.white200,
    flexDirection: 'row',
    borderRadius: 20,
    paddingHorizontal: 12,
    paddingVertical: 3,
    justifyContent: 'center',
    alignItems: 'center',
  },
  filterText: {
    fontSize: 12,
    color: '#636363',
    marginStart: 4,
    fontFamily: 'inter',
  },
});

export default FieldFilterSelector;