// MyCHIPs Mobile Application
// Copyright MyCHIPs.org
// TODO:
//- Connection:
//X-  Wrap websocket module
//X-  Can we do without origin in wsoptions?
//X-  entcli still works
//X- Can connect with token
//X- Save key locally when generated
//X- Can connect with saved key
//X- Status line shows connection state
//- Add real QR scanner screen
//- Read QR connection ticket (framework for other types)
//- Can launch from deep link to connection ticket
//- 

import React, { Component } from 'react';
import { Button, View, Text, StyleSheet, TouchableOpacity, Image, NativeModules } from 'react-native';
import { NavigationContainer } from '@react-navigation/native';
import { createNativeStackNavigator } from '@react-navigation/native-stack';
import PolyfillCrypto from 'react-native-webview-crypto'

const listen = ['mychips_user','wylib']		//Listen for these notifies from the DB
const httpPort = 8000
const wsPort = 54320
const Wm = require('./src/wyseman')
const Connect = require('./src/connect')
import ServIcon from './src/servicon'

import TallyInvite from './src/invite'

const ticket = require('./assets/ticket.json')
const debug = console.log
var conn = new Connect({
  webcrypto: window.crypto,
  httpPort, wsPort, listen,
  wm: Wm
})

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

function GlobalMenu(p) {
//console.log('HI:',p.nav)
  return (
    <View style={styles.global}>
      <TouchableOpacity style={styles.buttonBox} onPress={()=>{p.nav.navigate('Home')}}>
        <Image style={styles.button} source={require("./assets/icon-home.png")}/>
      </TouchableOpacity>
      <TouchableOpacity style={styles.buttonBox} onPress={()=>{p.nav.navigate('Receive')}}>
        <Image style={styles.button} source={require("./assets/icon-receive.png")}/>
      </TouchableOpacity>
      <TouchableOpacity style={styles.buttonBox} onPress={()=>{p.nav.navigate('Scan')}}>
        <Image style={styles.button} source={require("./assets/icon-scan.png")}/>
      </TouchableOpacity>
      <TouchableOpacity style={styles.buttonBox} onPress={()=>{p.nav.navigate('Invite')}}>
        <Image style={styles.button} source={require("./assets/icon-invite.png")}/>
      </TouchableOpacity>
      <TouchableOpacity style={styles.buttonBox} onPress={()=>{p.nav.navigate('Settings')}}>
        <Image style={styles.button} source={require("./assets/icon-settings.png")}/>
      </TouchableOpacity>
    </View>
  );
}

function HomeScreen({ navigation }) {
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
      <GlobalMenu nav={navigation} />
    </View>
  );
}

function ReceiveScreen({ navigation }) {
  return (
    <View style={{ flex: 1, alignItems: 'center', justifyContent: 'center' }}>
      <Text>Receive Screen</Text>
      <GlobalMenu nav={navigation} />
    </View>
  );
}

function ScanScreen(p) {
  return (
    <View style={{ flex: 1, alignItems: 'center', justifyContent: 'center' }}>
      <Text>Scan Screen</Text>
      <GlobalMenu nav={p.navigation} />
    </View>
  );
}

function InviteScreen({ navigation }) {
  return (
    <View style={{ flex: 1, alignItems: 'center', justifyContent: 'center' }}>
      <TallyInvite wm={Wm}/>
      <GlobalMenu nav={navigation} />
    </View>
  );
}

function SettingsScreen({ navigation }) {
  return (
    <View style={{ flex: 1, alignItems: 'center', justifyContent: 'center' }}>
      <Text>Settings Screen</Text>
      <GlobalMenu nav={navigation} />
    </View>
  );
}

const Stack = createNativeStackNavigator();

function App() {
  return (
    <NavigationContainer>
      <ServIcon wm={Wm}/>
      <PolyfillCrypto />
      <Stack.Navigator initialRouteName="Home">
        <Stack.Screen name="Home" component={HomeScreen} options={{title: 'Tallies'}}/>
        <Stack.Screen name="Receive" component={ReceiveScreen} />
        <Stack.Screen name="Scan" component={ScanScreen} />
        <Stack.Screen name="Invite" component={InviteScreen} />
        <Stack.Screen name="Settings" component={SettingsScreen} />
      </Stack.Navigator>
    </NavigationContainer>
  );
}

setTimeout(() => {
  console.log("W:", window)
}, 1000)

const styles = StyleSheet.create({
  global: {
    flex: 1,
    padding: 4,
    flexDirection: 'row',
    alignItems: 'center',
    justifyContent: 'center',
    position: 'absolute',
    bottom: 0,
  },
  buttonBox: {
    alignItems: 'center',
//    backgroundColor: '#e0e0e0',
    borderRadius: 8,
    flex: 1,
  },
  button: {
//    position: 'absolute',
//    padding: 10,
//    marginBottom: 20,
//    shadowColor: '#303838',
//    shadowOffset: { width: 0, height: 5 },
//    shadowRadius: 10,
//    shadowOpacity: 0.35,
  },
})

export default App;
