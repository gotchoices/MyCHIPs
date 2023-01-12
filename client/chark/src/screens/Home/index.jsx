import React, { useEffect, useState } from 'react';
import { View, Text, TouchableOpacity, Linking } from 'react-native'

import Button from '../../components/Button';

import useCurrentUser from '../../hooks/useCurrentUser';
import { parse } from '../../utils/query-string';
import { query_user } from '../../utils/user';

const Wm = require('../../../src/wyseman')

const ticket = require('../../../assets/ticket.json')

var pktId = 1
function query_users() {
  Wm.request(pktId++, 'select', {
    view: 'mychips.users_v_me',
    fields: ['id', 'std_name', 'peer_cid', 'peer_agent']
  }, data => {
console.log('Data:', JSON.stringify(data,null,2))
  })
}

const HomeScreen = ({ navigation, conn }) => {
  const { setUser } = useCurrentUser();

  const connect = (ticket) => {
    conn.connect(ticket, (err, connected) => {
      if(connected) {
        query_user().then((data) => {
          setUser(data?.[0]);
        })
      }
    })
  }

  useEffect(() => {
    Linking.getInitialURL().then((url) => {
      if(url) {
        const obj = parse(url);
        connect({ ticket: obj });
      }
    });

    const listener = Linking.addEventListener('url', ({url}) => {
      if(url) {
        const obj = parse(url);
        connect({ ticket: obj });
      }
    })

    return () => {
      conn.disconnect();
      listener.remove();
    };
  }, []);

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
    query_user().then((data) => {
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
        onPress={() => conn.disconnect()}
      />
      <Button
        title="Query Users"
        onPress={query_users}
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
