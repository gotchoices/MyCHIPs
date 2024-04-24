import React from "react"
import { Modal, StyleSheet, View, Text } from "react-native"
import { KeyboardAwareScrollView } from 'react-native-keyboard-aware-scroll-view';

const BottomSheetModal = (props) => {
  return (
    <Modal
      transparent={true}
      animationType="slide"
      visible={props.isVisible}
      onRequestClose={props.onClose}
    >
      <KeyboardAwareScrollView 
        enableOnAndroid
        keyboardShouldPersistTaps="handled" 
        contentContainerStyle={{flexGrow: 1}}
      >
        <View style={styles.container} >
          <View style={styles.content}>
            {props.children}
          </View>
        </View>
      </KeyboardAwareScrollView>
    </Modal>
  )
}

const styles = StyleSheet.create({
  container: {
    flex: 1,
    alignItems: 'center',
    justifyContent: 'flex-end',
    backgroundColor: 'rgba(0, 0, 0, 0.2)',
  },
  content: {
    backgroundColor: 'white',
    width: '100%',
    borderTopLeftRadius: 16,
    borderTopRightRadius: 16,
  }
});

export default BottomSheetModal;
