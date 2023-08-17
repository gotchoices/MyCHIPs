import React from 'react';
import { StyleSheet, Image, View } from 'react-native';
import { ProfileImage } from '../SvgAssets/SvgAssets';
import { colors } from '../../config/constants';

const Avatar = (props) => {
  return props.avatar ? (
    <Image
      source={{ uri: props.avatar }}
      style={[styles.image, props?.style ?? {}]}
    />
  ) : (<View style={[styles.image, props?.style ?? {}, { backgroundColor: colors.white }]}>
    <ProfileImage />
  </View>)
}

const styles = StyleSheet.create({
  image: {
    width: 100,
    height: 100,
    borderRadius: 50,
  }
});

export default Avatar;
