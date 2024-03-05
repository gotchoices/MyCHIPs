import React, { useEffect, useMemo } from 'react';
import {
  View,
  StyleSheet,
  ScrollView,
  Text,
} from 'react-native';
import { Buffer } from 'buffer';
import { useSelector, useDispatch } from 'react-redux';

import { colors } from '../../config/constants';
import useSocket from '../../hooks/useSocket';
import { uploadAvatar, fetchComm, fetchAddresses } from '../../redux/profileSlice';
import { useCommunication, useUser, useAddressV, useAddressVFlat } from '../../hooks/useLanguage';
import useMessageText from '../../hooks/useMessageText';

import Avatar from './Avatar';
import Details from './Details';
import PersonalBio from './PersonalBio';
import Address from './Address';
import Spinner from '../../components/Spinner';

const Profile = (props) => {
  const { wm } = useSocket();
  const dispatch = useDispatch();
  const { avatar, loadingAvatar, communications, personal }  = useSelector(state => state.profile);
  const { messageText } = useMessageText();
  const charkText = messageText?.chark?.msg;

  // Registering necessary text hooks for current language
  const commText = useCommunication(wm);
  useAddressV(wm);
  useAddressVFlat(wm);
  useUser(wm);

  const { user } = useSelector(state => state.currentUser);
  const user_ent = user?.curr_eid;

  useEffect(() => {
    if(charkText?.profile?.title) {
      props.navigation.setOptions({ title: charkText?.profile?.title })
    }
  }, [charkText?.profile?.title])

  useEffect(() => {
    dispatch(fetchComm({ wm, user_ent }))
    dispatch(fetchAddresses({ wm, user_ent }))
  }, [wm, user_ent])

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

  const uploadProfile = (data) => {
    let fileData = Buffer.from(data.data, 'base64')

    const payload = {
      file_fmt: data.fmt,
      file_data: fileData,
      file_cmt: 'Profile',
    };

    dispatch(uploadAvatar({ wm, payload }))
  }

  return (
    <ScrollView>
      <View style={styles.container}>
        <View style={styles.avatar}>
          {
            loadingAvatar 
              ? <Spinner />
              : <Avatar 
                  avatar={avatar}
                  uploadProfile={uploadProfile}
                />
          }

          <Text style={{ color: colors.black, marginTop: 16, fontSize: 18, fontWeight: 'bold', alignSelf: 'center' }}>
            {personal?.cas_name}
          </Text>
        </View>

        <View style={{ marginBottom: 16 }}>
          <Details
            title={commText?.email_comm?.title ?? ''}
            helpText={commText?.email_comm?.help ?? ''}
            rowField="comm_spec"
            primaryField="comm_prim"
            items={emails}
            onEditPress={onEditPress('email', 'Edit Email')}
          />
        </View>

        <View style={{ marginBottom: 16 }}>
          <Details
            title={commText?.phone_comm?.title ?? ''}
            helpText={commText?.phone_comm?.help ?? ''}
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

