import React, { useEffect } from 'react';
import { Text } from 'react-native';

import Comm from './Comm';
import PersonalBio from './PersonalBio';

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
        wm={props.wm}
        profileType="email"
      />
    )
  } 

  if(profileType === 'phone') {
    return (
      <Comm 
        wm={props.wm}
        profileType="phone"
      />
    )
  } 

  if(profileType === 'personal') {
    return (
      <PersonalBio
        wm={props.wm}
      />
    )
  } 

  return (
    <Text>Invalid Profile type</Text>
  );
}



export default ProfileEdit;
