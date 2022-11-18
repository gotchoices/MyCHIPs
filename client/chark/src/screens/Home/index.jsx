import React, { useEffect } from 'react';
import { View, Text, Button, TouchableOpacity, Linking } from 'react-native'

import { parse } from '../../utils/query-string';

const ticket = require('../../../assets/ticket.json')

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
    </View>
  );
}

export default HomeScreen;
