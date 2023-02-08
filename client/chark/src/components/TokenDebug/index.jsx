// Used only for debugging purposes
import React from 'react';
import { View, Text } from 'react-native'
import PropTypes from 'prop-types';

import Button from '../../components/Button';

import { parse } from '../../utils/query-string';
import { query_user } from '../../utils/user';
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

const TokenDebug = (props) => {
  const { connectSocket, disconnectSocket, wm } = useSocket();

  const connect = (ticket) => {
    connectSocket(ticket);
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
        title="Cancel"
        onPress={props.onCancel}
      />
    </View>
  );
}

TokenDebug.propTypes = {
  onCancel: PropTypes.func.isRequired,
}

export default TokenDebug;
