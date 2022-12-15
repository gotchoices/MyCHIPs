import React, { useState } from 'react';
import { Image, View, StyleSheet, TouchableOpacity, Modal, Text } from 'react-native';
import ImagePicker, {ImageOrVideo} from 'react-native-image-crop-picker';

import { colors } from '../../../config/constants';
import profileImg from '../../../../assets/profile.png';

const Avatar = (props) => {
  const [isVisible, setIsVisible] = useState(false);

  const openModal = () => {
    setIsVisible(true);
  }

  const closeModal = () => {
    setIsVisible(false);
  }

  const openPicker = () => {
    ImagePicker.openPicker({
      width: 300,
      height: 300,
      cropping: true,
      cropperCircleOverlay: true,
      freeStyleCropEnabled: true,	
    }).then(image => {
      props.setAvatar(image.path)
    }).catch(console.log)
    .finally(() => {
      closeModal()
    });
  }

  const openCamera = () => {
    ImagePicker.openCamera({
      width: 300,
      height: 300,
      cropping: true,
      cropperCircleOverlay: true,
      freeStyleCropEnabled: true,	
    }).then(image => {
      setAvatar(image.path)
    }).catch(console.log)
    .finally(() => {
      closeModal()
    });
  }

  return(
    <>
      <View style={styles.profile}>
        <TouchableOpacity
          onPress={openModal}
        >
          <Image
            style={styles.profileImage}
            source={props.avatar ? { uri: props.avatar }: profileImg} 
          />
        </TouchableOpacity>
      </View>

      <Modal
        visible={isVisible}
        animationType="slide"
        onBackButtonPress={closeModal}
        onBackdropPress={closeModal}
        onRequestClose={closeModal}
      >
        <View style={styles.modalContainer}>
          <View style={styles.modalView}>
            <View style={styles.sources}>
              <TouchableOpacity style={styles.option} onPress={openPicker}>
                <Text style={styles.sourceText}>Library</Text>
              </TouchableOpacity>

              <TouchableOpacity style={styles.option} onPress={openCamera}>
                <Text style={styles.sourceText}>Camera</Text>
              </TouchableOpacity>
            </View>
          </View>
        </View>
      </Modal>
    </>
  )
}

const styles = StyleSheet.create({
  profile: {
    alignItems: 'center',
  },
  profileImage: {
    width: 100,
    height: 100,
    borderRadius: 50,
  },
  modalContainer: {
    flex: 1,
    backgroundColor: 'rgba(0, 0, 0, 0.3)',
    justifyContent: "flex-end",
  },
  modalView: {
    backgroundColor: colors.white,
    borderTopRightRadius: 30,
    borderTopLeftRadius: 30,
    padding: 35,
    paddingTop: 24,
    shadowColor: 'black',
    shadowOffset: {
      width: 2,
      height: 3
    },
    shadowOpacity: 0.25,
    shadowRadius: 4,
    elevation: 15 
  },
  sourceText: {
    color: colors.black,
    alignSelf: 'center',
  },
  sources: {
    marginTop: 32,
    flexDirection: 'row',
    alignItems: "center",
  },
  option: {
    flex: 1,
    justifyContent: 'center',
    alignItems: 'center',
  },
  sourceText: {
    color: colors.black,
    fontSize: 16,
  },
})

export default Avatar;
