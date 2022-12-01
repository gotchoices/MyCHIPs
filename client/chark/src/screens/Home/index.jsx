import React, { useEffect, useState } from 'react';
import { View, Text, Button, TouchableOpacity, Linking } from 'react-native'

import { parse } from '../../utils/query-string';

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
function query_user() {
  Wm.request(pktId++, 'select', {
    view: 'base.ent_v',
    table: 'base.curr_eid',
    params: []
  }, data => {
console.log('Data:', JSON.stringify(data,null,2))
  })
}


const HomeScreen = ({ navigation, conn }) => {
  useEffect(() => {
    Linking.getInitialURL().then((url) => {
      if(url) {
        const obj = parse(url);
        conn.connect({
          ticket: obj,
        })
      }
    });

    const listener = Linking.addEventListener('url', ({url}) => {
      if(url) {
        const obj = parse(url);
        conn.connect({
          ticket: obj,
        })
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

  return (
    <View style={{ flex: 1, alignItems: 'center', justifyContent: 'center' }}>
      <Text>Home Screen</Text>
      <Button
        title="Connect with Token"
        onPress={() => conn.connect(ticket)}
      />
      <Button
        title="Connect with Key"
        onPress={() => conn.connect()}
      />
      <Button
        title="Disconnect"
        onPress={() => conn.disconnect()}
      />
      <Button
        title="Query Users"
        onPress={() => query_users()}
      />
      <Button
        title="Query Session User"
        onPress={() => query_user()}
      />
      <Button
        title="Get Tallies"
        onPress={() => getTallies()}
      />
    </View>
  );
}

export default HomeScreen;
