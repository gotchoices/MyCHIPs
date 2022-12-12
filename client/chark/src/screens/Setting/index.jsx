import React from 'react';
import { View, TouchableWithoutFeedback, Text, StyleSheet, Image, Button } from 'react-native';

import { colors } from '../../config/constants';

import profileImg from '../../../assets/profile.png';

const Setting = (props) => {
  const onProfilePress = () => {
    props.navigation.navigate('Profile');
  }

  return (
    <View style={styles.container}>
      <View style={styles.profile}>
        <Image
          style={styles.profileImage}
          source={profileImg} 
        />

        <Text style={styles.name}>
          John Doe
        </Text>

        <Button
          title="Edit profile"
          onPress={onProfilePress}
        />

      </View>
    </View>
  )
}

const styles = StyleSheet.create({
  container: {
    flex: 1,
    paddingVertical: 16,
  },
  profile: {
    marginHorizontal: 16,
    paddingVertical: 24,
    alignItems: 'center',
    backgroundColor: colors.white,
  },
  profileImage: {
    width: 100,
    height: 100,
    borderRadius: 50,
  },
  name: {
    color: colors.black,
    fontSize: 24,
  }
});

export default Setting;
