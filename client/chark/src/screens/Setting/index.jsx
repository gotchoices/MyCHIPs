import React, { useEffect } from 'react';
import { View, Text, StyleSheet, Image, Button } from 'react-native';

import { colors } from '../../config/constants';
import useCurrentUser from '../../hooks/useCurrentUser';
import useProfile from '../../hooks/useProfile';
import { getPersonal } from '../../services/profile';

import profileImg from '../../../assets/profile.png';

const Setting = (props) => {
  const { user } = useCurrentUser();
  const user_ent = user?.curr_eid;
  const {
    personal,
    setPersonal,
  } = useProfile();

  useEffect(() => {
    getPersonal(props.wm, user_ent).then(data => {
      setPersonal(data);
    });
  }, [])

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
          {personal?.cas_name}
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
    marginVertical: 16,
    fontSize: 18,
    fontWeight: 'bold',
    alignSelf: 'center',
  }
});

export default Setting;
