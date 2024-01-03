import React from 'react';
import { View, Text, StyleSheet, ScrollView } from 'react-native';

import ActiveKey from './ActiveKey';
import GenerateKey from './GenerateKey';
import ImportKey from './ImportKey';
import Export from './Export';

import { colors } from '../../config/constants';

const KeyManagement = (props) => {

  return (
    <ScrollView
      style={styles.container}
      contentContainerStyle={styles.contentContainer}
    >
      <View style={{ marginBottom: 30 }}>
        <Text style={styles.description}>
          Tallies are linked to keys. When establishing a tally 
          that tally can only operate with the key that it was 
          created with. Make sure to export your current
          active key when performing destructive actions.
        </Text>
      </View>

      <ActiveKey />

      <GenerateKey />

      <ImportKey navigation={props.navigation} />

      <Export />
    
    </ScrollView>
  )
}

const styles = StyleSheet.create({
  container: {
    flex: 1,
  },
  contentContainer: {
    padding: 20,
  },
  description: {
    fontFamily: 'inter',
    fontWeight: '500',
    textAlign: 'center',
    color: colors.black,
    fontSize: 13,
    lineHeight: 18,
  },
});

export default KeyManagement;
