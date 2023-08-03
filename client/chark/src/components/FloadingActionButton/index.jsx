import React from 'react';
import { View, TouchableOpacity, Text, StyleSheet } from 'react-native';
import { AddIcon } from '../SvgAssets/SvgAssets';

const FloatingActionButton = ({ onPress }) => {
  return (
    <TouchableOpacity style={styles.fab} onPress={onPress}>
      <View style={styles.fabContent}>
        <AddIcon size={23} />
      </View>
    </TouchableOpacity>
  );
};

const styles = StyleSheet.create({
  fab: {
    position: 'absolute',
    bottom: 16,
    right: 16,
    width: 56,
    height: 56,
    borderRadius: 28,
    backgroundColor: '#155CEF',
    alignItems: 'center',
    justifyContent: 'center',
    elevation: 6,
  },
  fabContent: {
    alignItems: 'center',
    justifyContent: 'center',
  },
});

export default FloatingActionButton;
