import React from 'react';
import {
  View,
  Modal,
  StyleSheet,
} from 'react-native';
import PropTypes from 'prop-types';

import { colors } from '../../config/constants';

const CenteredModal = (props) => {
  return (
    <Modal
      animationType="slide"
      transparent={true}
      visible={props.isVisible}
      onRequestClose={props.onClose}
    >
      <View style={styles.centeredView}>
        <View style={styles.modalView}>
          {props.children}
        </View>
      </View>
    </Modal>
  )
}
const styles = StyleSheet.create({
  centeredView: {
    flex: 1,
    alignItems: "center",
    justifyContent: "center",
    backgroundColor: 'rgba(0, 0, 0, 0.3)',
  },
  modalView: {
    width: '92%',
    height: '90%',
    paddingVertical: 20,
    backgroundColor: colors.white,
    borderRadius: 20,
    alignItems: "center",
    shadowColor: "#000",
    shadowOffset: {
      width: 0,
      height: 2
    },
    shadowOpacity: 0.25,
    shadowRadius: 4,
    elevation: 5
  },
});

CenteredModal.propTypes = {
  isVisible: PropTypes.bool.isRequired,
  onClose: PropTypes.func.isRequired,
}

export default CenteredModal;
