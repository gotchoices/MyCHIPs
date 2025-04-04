import React, { useState } from 'react';
import { View, Text, StyleSheet, TouchableOpacity, ScrollView } from 'react-native';
import PropTypes from 'prop-types';
import BottomSheetModal from '../BottomSheetModal';
import FilterItem from './FilterItem';
import { colors } from '../../config/constants';

/**
 * Modal component for displaying filter options
 * Shows a list of options with checkboxes that can be selected
 */
const FilterModal = ({ 
  visible, 
  options, 
  selectedValues,
  fieldName,
  buttonLabel,
  onClose,
  onSave
}) => {
  const [selections, setSelections] = useState(selectedValues || []);
  
  const toggleOption = (value) => {
    const newSelections = [...selections];
    
    if (newSelections.includes(value)) {
      // Remove if already selected
      const index = newSelections.indexOf(value);
      newSelections.splice(index, 1);
    } else {
      // Add if not selected
      newSelections.push(value);
    }
    
    setSelections(newSelections);
  };

  // Removed Select All/Clear functionality
  
  return (
    <BottomSheetModal isVisible={visible} onClose={onClose}>
      <View style={styles.container}>
        <View style={styles.header}>
          <Text style={styles.title}>{buttonLabel || fieldName}</Text>
        </View>
        
        <ScrollView style={styles.list}>
          {options.map((item, index) => (
            <React.Fragment key={item.value}>
              <FilterItem
                option={item}
                isSelected={selections.includes(item.value)}
                onToggle={() => toggleOption(item.value)}
              />
              {index < options.length - 1 && <View style={styles.divider} />}
            </React.Fragment>
          ))}
        </ScrollView>
        
        <View style={styles.footer}>
          <TouchableOpacity style={styles.cancelButton} onPress={onClose}>
            <Text style={styles.cancelText}>✕</Text>
          </TouchableOpacity>
          
          <TouchableOpacity 
            style={styles.applyButton}
            onPress={() => onSave(selections)}
          >
            <Text style={styles.applyText}>✓</Text>
          </TouchableOpacity>
        </View>
      </View>
    </BottomSheetModal>
  );
};

FilterModal.propTypes = {
  visible: PropTypes.bool.isRequired,
  options: PropTypes.arrayOf(
    PropTypes.shape({
      value: PropTypes.string.isRequired,
      title: PropTypes.string.isRequired
    })
  ).isRequired,
  selectedValues: PropTypes.arrayOf(PropTypes.string),
  fieldName: PropTypes.string.isRequired,
  buttonLabel: PropTypes.string,
  onClose: PropTypes.func.isRequired,
  onSave: PropTypes.func.isRequired
};

const styles = StyleSheet.create({
  container: {
    paddingVertical: 16,
  },
  header: {
    paddingHorizontal: 24,
    paddingVertical: 16,
    borderBottomWidth: 1,
    borderBottomColor: colors.lightgray,
  },
  title: {
    fontSize: 18,
    fontWeight: '600',
    color: colors.black100,
    fontFamily: 'inter',
    textAlign: 'center',
  },
  list: {
    maxHeight: 300,
  },
  divider: {
    height: 1,
    width: '100%',
    backgroundColor: colors.lightgray,
  },
  footer: {
    flexDirection: 'row',
    justifyContent: 'space-between',
    paddingHorizontal: 24,
    paddingTop: 16,
    borderTopWidth: 1,
    borderTopColor: colors.lightgray,
  },
  cancelButton: {
    padding: 12,
    width: 50,
    alignItems: 'center',
  },
  cancelText: {
    color: colors.gray500,
    fontSize: 20,
    fontFamily: 'inter',
  },
  applyButton: {
    padding: 12,
    width: 50,
    alignItems: 'center',
    backgroundColor: colors.blue,
    borderRadius: 8,
  },
  applyText: {
    color: colors.white,
    fontSize: 20,
    fontFamily: 'inter',
  },
});

export default FilterModal;