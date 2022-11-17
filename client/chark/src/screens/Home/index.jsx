import React from 'react';
import { View, Text, Button, TouchableOpacity } from 'react-native'

const ticket = require('../../../assets/ticket.json')

const HomeScreen = ({ navigation, conn }) => {
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
