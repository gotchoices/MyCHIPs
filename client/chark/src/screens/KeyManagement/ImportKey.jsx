import React, { useState } from 'react';
import { View, Text, StyleSheet } from 'react-native';

import Button from '../../components/Button';
import SigningKeyWarning from '../../components/SigningKeyWarning';
import BottomSheetModal from '../../components/BottomSheetModal';

import { colors } from '../../config/constants';

const ImportKey = (props) => {
  const [showImportWarning, setShowImportWarning] = useState(false);

  const onImportClick = () => {
    setShowImportWarning(true);
  }

  const onImportCancel = () => {
    setShowImportWarning(false);
  }

  const onAccept = () => {
    setShowImportWarning(false);
    props.navigation.navigate('ImportKey')
  }

  return (
    <>
      <View style={{ marginTop: 30 }}>
        <Text style={styles.importText}>{props?.importText}</Text>
        <Text style={styles.importDescription}>
          Importing a new key can be a destructive action. Remember to save your current active key by exporting it to a safe place.
        </Text>

        <Button
          style={styles.importBtn}
          title={props?.importText}
          onPress={onImportClick}
        />

      </View>

      <BottomSheetModal
        isVisible={showImportWarning}
        onClose={onImportCancel}
      >
        <SigningKeyWarning
          loading={false}
          title="Importing a new key is a destructive action"
          description={`When you open a tally it is signed with a key and needs that key to operate.\n\nIt’s recommended to export and save your keys before you Import new ones.`}
          onAccept={onAccept}
          onCancel={onImportCancel}
        />
      </BottomSheetModal>
    </>
  )
}

const styles = StyleSheet.create({
  importText: {
    color: colors.black,
    fontSize: 15,
    fontFamily: 'inter',
    fontWeight: '500',
  },
  importDescription: {
    color: colors.gray300,
    fontWeight: '500',
    fontFamily: 'inter',
    fontSize: 12,
    lineHeight: 13,
  },
  importBtn: {
    marginTop: 16,
    width: '50%',
    height: 30,
  },
});

export default ImportKey;
