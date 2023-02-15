import React, { useEffect, useState, useCallback } from 'react';
import { View, Text, TouchableOpacity, Linking } from 'react-native'
import { useFocusEffect } from '@react-navigation/native';

import Tally from '../Tally';
import Button from '../../components/Button';

import { parse } from '../../utils/query-string';
import { query_user } from '../../utils/user';
import { getLinkHost } from '../../utils/common';
import useSocket from '../../hooks/useSocket';
import TokenDebug from '../../components/TokenDebug';

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

const connectionUri = new Set(['connect', 'mychips.org/connect'])
const HomeScreen = (props) => {
  const { connectSocket, disconnectSocket, wm, ws } = useSocket();

  const connect = (ticket) => {
    connectSocket(ticket);
  }

  useEffect(() => {
    Linking.getInitialURL().then((url) => {
      const host = getLinkHost(url ?? '');
      if(!connectionUri.has(host)) {
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
        if(!connectionUri.has(host)) {
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

  return (
    <View style={{ flex: 1 }}>
      <Tally navigation={props.navigation} />
    </View>
  );
}

export default HomeScreen;
