import React, { useEffect, useState, useCallback } from 'react';
import { View, Text, TouchableOpacity, Linking } from 'react-native'
import { useFocusEffect } from '@react-navigation/native';

import Button from '../../components/Button';

import useCurrentUser from '../../hooks/useCurrentUser';
import { parse } from '../../utils/query-string';
import { query_user } from '../../utils/user';
import { getLinkHost } from '../../utils/common';
import useSocket from '../../hooks/useSocket';

const ticket = require('../../../assets/ticket.json')

var pktId = 1
function query_users(wm) {
  wm.request(pktId++, 'select', {
    view: 'mychips.users_v_me',
    fields: ['id', 'std_name', 'peer_cid', 'peer_agent']
  }, data => {
console.log('Data:', JSON.stringify(data,null,2))
  })
}

const HomeScreen = ({ navigation, ...props }) => {
  const { setUser } = useCurrentUser();
  const { connectSocket, disconnectSocket, wm, ws } = useSocket();

  const connect = (ticket) => {
    connectSocket(ticket);
  }

  useEffect(() => {
    Linking.getInitialURL().then((url) => {
      const host = getLinkHost(url ?? '');
      if(host !== 'connect') {
        return;
      }

      const obj = parse(url);
      connect({ ticket: obj });
    });

  }, []);


  useFocusEffect(
    useCallback(() => {
      const listener = Linking.addEventListener('url', ({url}) => {
        const host = getLinkHost(url ?? '');
        if(host !== 'connect') {
          return;
        }

        const obj = parse(url);
        connect({ ticket: obj });
      })

      return () => {
        listener.remove();
      };

    }, [])
  );

  const getTallies = () => {
    navigation.navigate('Tallies')
  }

  const connectWithToken = () => {
    connect(ticket);
  }

  const connectWithKey = () => {
    connect(null)
  }

  const querySessionUser = () => {
    query_user(wm).then((data) => {
      console.log(JSON.stringify(data, null, 2))
    })
  }

  return (
    <View style={{ flex: 1, alignItems: 'center', justifyContent: 'center' }}>
      <Text>Home Screen</Text>
      <Button
        title="Connect with Token"
        onPress={connectWithToken}
      />
      <Button
        title="Connect with Key"
        onPress={connectWithKey}
      />
      <Button
        title="Disconnect"
        onPress={() => disconnectSocket()}
      />
      <Button
        title="Query Users"
        onPress={() => query_users(wm)}
      />
      <Button
        title="Query Session User"
        onPress={querySessionUser}
      />
      <Button
        title="Get Tallies"
        onPress={() => getTallies()}
      />
    </View>
  );
}

export default HomeScreen;
