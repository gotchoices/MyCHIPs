import React, { useEffect } from 'react';
import { Text } from 'react-native';

import Comm from './Comm';
import PersonalBio from './PersonalBio';
import Address from './Address';

const ProfileEdit = (props) => {
  const { profileType, title } = props.route?.params;

  useEffect(() => {
    props.navigation.setOptions({
      title,
    });
  }, [])

  if(profileType === 'email') {
    return (
      <Comm 
        profileType="email"
      />
    )
  } 

  if(profileType === 'phone') {
    return (
      <Comm 
        profileType="phone"
      />
    )
  } 

  if(profileType === 'personal') {
    return (
      <PersonalBio />
    )
  } 

  if(profileType === 'address') {
    return (
      <Address />
    )
  } 

  return (
    <Text>Invalid Profile type</Text>
  );
}



export default ProfileEdit;
