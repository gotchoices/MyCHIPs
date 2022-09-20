// MyCHIPs Mobile Application
// Copyright MyCHIPs.org
// TODO:
//- Connection:
//X-  Wrap websocket module
//X-  Can we do without origin in wsoptions?
//X-  entcli still works
//- Can connect with token
//- Save key locally when generated
//- Can connect with saved key
//- 
//- Add real scanner screen
//- Read connection ticket (framework for other types)
//- How to access global resources (context)
//- 
//- 

import React, { Component } from 'react';
import { Button, View, Text, StyleSheet, TouchableOpacity, Image, NativeModules } from 'react-native';
import { NavigationContainer } from '@react-navigation/native';
import { createNativeStackNavigator } from '@react-navigation/native-stack';
import PolyfillCrypto from 'react-native-webview-crypto'

const ClientAPI = require('wyseman/lib/client_ws')
const Wm = require('./src/wyseman')
const listen = ['mychips_user','wylib']		//Listen for these notifies from the DB
const httpPort = 8000
const wsPort = 54320

const myFetch = function(uri, options) {
  console.log("Local fetch")
  return fetch(uri, options)
}
const debug = console.log
var ws

console.log('Crypto:', window.crypto.subtle)
function connect(tok) {
  let ticket = require('./assets/ticket.json')
    , api = new ClientAPI({
        webcrypto: window.crypto,
        listen,
        httpPort, 
        fetch: myFetch,
        saveKey: () => {
debug("Writing connection key to localStorage:")
        },
        debug:				console.log
      })
    , creds = Object.assign({user: 'admin'}, ticket.ticket)
    , address = `${creds.host}:${wsPort}`
    , origin = `https://${creds.host}:${httpPort}`

console.log('Pre:', creds)
  api.uri(creds).then(wsURI => {			//Build connection URI	
debug('Connect:', wsURI)
    ws = new WebSocket(wsURI)				//Open websocket to backend

    ws.onclose = () => Wm.onClose()
    ws.onopen = () => Wm.onOpen(address, m => {
      ws.send(m)
    })
    ws.onerror = err => {
      Wm.onClose()
debug("Connection failed:", err.message)
    }
    ws.onmessage = e => Wm.onMessage(e.data)

    Wm.register('wylib0', 'wylib.data', (data, err) => {
debug("Backend supplies wylib data:", !!data, "err:", err)
    })
  }).catch(err => {
debug('Error initializing', err.message)
  })	// api.uri()
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
        onPress={() => connect(true)}
      />
      <Button
        title="Connect with Key"
        onPress={() => connect(false)}
      />
      <Button
        title="Query Backend"
        onPress={() => query()}
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
      <Text>Invite Screen</Text>
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

//    <View>
//    </View>
function App() {
  return (
      <NavigationContainer>
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
