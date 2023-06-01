import React, { useState, useEffect, useMemo } from 'react';
import {
  View,
  StyleSheet,
  ScrollView,
  Text,
} from 'react-native';

import { colors } from '../../config/constants';
import useSocket from '../../hooks/useSocket';

import useCurrentUser from '../../hooks/useCurrentUser';
import useProfile from '../../hooks/useProfile';
import { useProfileText } from '../../hooks/useLanguage';
import { getComm, getAddresses, getProfileText} from '../../services/profile';

import Avatar from './Avatar';
import Details from './Details';
import PersonalBio from './PersonalBio';
import Address from './Address';

const Profile = (props) => {
  const [avatar, setAvatar] = useState(undefined);
  const { wm } = useSocket();

  const {
    communications,
    personal,
    setPersonal,
    setCommunications,
    setAddresses,
  } = useProfile();
  const profileText = useProfileText(wm);

  const { user } = useCurrentUser();
  const user_ent = user?.curr_eid;

  useEffect(() => {
    getComm(wm, user_ent).then(data => {
      setCommunications(data);
    })

    getAddresses(wm, user_ent).then(data => {
      setAddresses(data);
    })
  }, [])

  const emails = useMemo(() => {
    return communications.filter((comm) => {
      return comm.comm_type === 'email';
    })
  }, [communications])

  const phones = useMemo(() => {
    return communications.filter((comm) => {
      return comm.comm_type === 'phone';
    })
  }, [communications])

  const onEditPress = (profileType, title) => {
    return () => {
      props.navigation.navigate('ProfileEdit', {
        profileType,
        title,
      })
    }
  } 

  return (
    <ScrollView>
      <View style={styles.container}>
        <View style={styles.avatar}>
          <Avatar />

          <Text style={{ color: colors.black, marginTop: 16, fontSize: 18, fontWeight: 'bold', alignSelf: 'center' }}>
            {personal?.cas_name}
          </Text>
        </View>

        <View style={{ marginBottom: 16 }}>
          <Details
            title={profileText?.email_comm?.title ?? ''}
            helpText={profileText?.email_comm?.help ?? ''}
            rowField="comm_spec"
            primaryField="comm_prim"
            items={emails}
            onEditPress={onEditPress('email', 'Edit Email')}
          />
        </View>

        <View style={{ marginBottom: 16 }}>
          <Details
            title={profileText?.phone_comm?.title ?? ''}
            helpText={profileText?.phone_comm?.help ?? ''}
            rowField="comm_spec"
            primaryField="comm_prim"
            items={phones}
            onEditPress={onEditPress('phone', 'Edit Phone')}
          />
        </View>

        <View style={{ marginBottom: 16 }}>
          <PersonalBio
            navigation={props.navigation}
          />
        </View>

        <View style={{ marginBottom: 16 }}>
          <Address
            navigation={props.navigation}
          />
        </View>
      </View>
    </ScrollView>
  )
}

const styles = StyleSheet.create({
  container: {
    flex: 1,
    margin: 10,
    padding: 10,
  },
  avatar: {
    padding: 16,
    marginBottom: 12,
    backgroundColor: colors.white,
  }
});

export default Profile;

