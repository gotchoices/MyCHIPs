import React, { useState } from 'react';
import { Image, View, StyleSheet, TouchableOpacity, Modal, Text } from 'react-native';
import ImagePicker, {ImageOrVideo} from 'react-native-image-crop-picker';

import { colors } from '../../../config/constants';
import profileImg from '../../../../assets/profile.png';

const Avatar = (props) => {
  const [avatar, setAvatar] = useState('');
  const [isVisible, setIsVisible] = useState(false);

  const openModal = () => {
    setIsVisible(true);
  }

  const closeModal = () => {
    setIsVisible(false);
  }
  console.log(isVisible)

  const openPicker = () => {
    ImagePicker.openPicker({
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
            source={avatar ? { uri: avatar }: profileImg} 
          />
        </TouchableOpacity>
      </View>

      <Modal
        visible={isVisible}
        animationType="fade"
        onBackButtonPress={closeModal}
        onBackdropPress={closeModal}
        onRequestClose={closeModal}
      >
        <View style={styles.source}>
          <View style={styles.modalView}>
            <TouchableOpacity style={styles.option} onPress={openPicker}>
              <Text style={styles.sourceText}>Library</Text>
            </TouchableOpacity>
            <TouchableOpacity style={styles.option} onPress={openCamera}>
              <Text style={styles.sourceText}>Camera</Text>
            </TouchableOpacity>
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
  source: {
    flex: 1,
    justifyContent: "flex-end",
  },
  modalView: {
    flexDirection: 'row',
    backgroundColor: colors.white,
    borderTopRightRadius: 30,
    borderTopLeftRadius: 30,
    padding: 35,
    alignItems: "center",
    shadowColor: 'black',
    shadowOffset: {
      width: 2,
      height: 3
    },
    shadowOpacity: 0.25,
    shadowRadius: 4,
    elevation: 15 
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
