import React from 'react';
import { StyleSheet, Image } from 'react-native';

import profileImg from '../../../assets/profile.png';

const Avatar = (props) => {
  return (
    <Image 
      source={props.avatar ? {uri: props.avatar} : profileImg}
      style={[styles.image, props?.style ?? {}]} 
    />
  )
}

const styles = StyleSheet.create({
  image: {
    width: 100,
    height: 100,
    borderRadius: 50,
  }
});

export default Avatar;
