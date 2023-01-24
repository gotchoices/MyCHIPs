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

import React, { Component, useEffect, useState } from 'react';
import { Button, View, Text, StyleSheet, TouchableOpacity, Image, NativeModules, Linking, AppState, TouchableWithoutFeedback, SafeAreaView } from 'react-native';
import { NavigationContainer } from '@react-navigation/native';
import { createNativeStackNavigator } from '@react-navigation/native-stack';
import PolyfillCrypto from 'react-native-webview-crypto'
import AsyncStorage from '@react-native-async-storage/async-storage'
import Toast from 'react-native-toast-message';

import ServIcon from './src/servicon'
import { parse } from './src/utils/query-string';
import constants from './src/config/constants';

//import TallyInvite from './src/invite'
import Invite from './src/screens/Invite'
import Home from './src/screens/Home';
import Scanner from './src/screens/Scanner';
import Tally from './src/screens/Tally';
import EditDraftTally from './src/screens/Tally/EditDraftTally';
import EditOpenTally from './src/screens/Tally/EditOpenTally';
import TallyReport from './src/screens/Tally/TallyReport';
import Setting from './src/screens/Setting';
import Profile from './src/screens/Profile';
import UserProvider from './src/components/UserProvider';
import ProfileProvider from './src/components/ProfileProvider';
import ProfileEdit from './src/screens/Profile/ProfileEdit';
import TallyAccept from './src/screens/TallyAccept';

const Connect = require('./src/connect')

const listen = ['mychips_user','wylib']		//Listen for these notifies from the DB
const Wm = require('./src/wyseman')

const debug = console.log
var conn = new Connect({
  webcrypto: window.crypto,
  listen: listen,
  wm: Wm
})

function GlobalMenu(p) {
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
      <Home conn={conn} navigation={navigation} />
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

function ScanScreen({ navigation }) {
  return (
    <View style={{ flex: 1, alignItems: 'center', justifyContent: 'center' }}>
      <Scanner conn={conn} navigation={navigation} />
      <GlobalMenu nav={navigation} />
    </View>
  );
}

function InviteScreen({ navigation }) {
  return (
    <View style={{ flex: 1 }}>
      <Invite wm={Wm} navigation={navigation} />
      <GlobalMenu nav={navigation} />
    </View>
  );
}

function SettingsScreen({ navigation }) {
  return (
    <View style={{ flex: 1 }}>
      <Setting wm={Wm} navigation={navigation} />
      <GlobalMenu nav={navigation} />
    </View>
  );
}

function TallyScreen({ navigation }) {
  return (
    <View style={{ flex: 1 }}>
      <Tally wm={Wm} navigation={navigation} />
      <GlobalMenu nav={navigation} />
    </View>
  );
}

function TallyReportScreen({ navigation }) {
  return (
    <View style={{ flex: 1 }}>
      <TallyReport wm={Wm} navigation={navigation} />
      <GlobalMenu nav={navigation} />
    </View>
  );
}

function TallyEditScreen({ route, navigation }) {
  const { tally_seq, tally_ent } = route.params;

  return (
    <View style={{ flex: 1 }}>
      <EditDraftTally wm={Wm} tally_seq={tally_seq} tally_ent={tally_ent} />
      <GlobalMenu nav={navigation} />
    </View>
  );
}

function OpenTallyEditScreen({ route, navigation }) {
  const { tally_seq, tally_ent } = route.params;

  return (
    <View style={{ flex: 1 }}>
      <EditOpenTally wm={Wm} tally_seq={tally_seq} tally_ent={tally_ent} />
      <GlobalMenu nav={navigation} />
    </View>
  );
}

function ProfileScreen(props) {
  return (
    <View style={{ flex: 1 }}>
      <Profile wm={Wm} {...props} />
      <GlobalMenu nav={props.navigation} />
    </View>
  );
}

function ProfileEditScreen(props) {
  return (
    <View style={{ flex: 1 }}>
      <ProfileEdit wm={Wm} {...props} />
      <GlobalMenu nav={props.navigation} />
    </View>
  );
}

function TallyAcceptScreen(props) {
  return (
    <View style={{ flex: 1 }}>
      <TallyAccept wm={Wm} {...props} />
      <GlobalMenu nav={props.navigation} />
    </View>
  );
}

const Stack = createNativeStackNavigator();
const linking = {
  prefixes: ["mychips://"],
  config: {
    screens:{
      Home: {
        path: 'connect',
      },
      TallyAccept: {
        path: 'tally-accept',
      }
    },
  },
};  

function App() {
  const [loading, setLoading] = useState(false);

  useEffect(() => {
    if(!conn.ws) {
      setLoading(true);
      conn.connect(null, (err, connected) => {
        setLoading(false);

        if(err) {
          console.log('Error connecting using key: ', err)
          return;
        } 
      });
    }
  }, []);

  return (
    <SafeAreaView style={{ flex: 1 }}>
    <NavigationContainer linking={linking}>
      <ServIcon wm={Wm} connecting={loading} />
      <PolyfillCrypto />
        <UserProvider>
          <ProfileProvider wm={Wm}>
            <Stack.Navigator initialRouteName="Home">
              <Stack.Screen name="Home" component={HomeScreen} options={{title: 'Tallies'}}/>
              <Stack.Screen name="Receive" component={ReceiveScreen} />
              <Stack.Screen name="Scan" component={ScanScreen} />
              <Stack.Screen name="Invite" component={InviteScreen} />
              <Stack.Screen name="Settings" component={SettingsScreen} />
              <Stack.Screen name="Tallies" component={TallyScreen} />
              <Stack.Screen name="TallyReport" component={TallyReportScreen} />
              <Stack.Screen name="TallyEdit" component={TallyEditScreen} options={{ title: 'Draft Tally' }} />
              <Stack.Screen name="OpenTallyEdit" component={OpenTallyEditScreen} options={{ title: 'Open Tally' }} />
              <Stack.Screen name="Profile" component={ProfileScreen} options={{ title: 'Profile' }} />
              <Stack.Screen name="ProfileEdit" component={ProfileEditScreen} options={{ title: 'Edit Profile' }} />
              <Stack.Screen name="TallyAccept" component={TallyAcceptScreen} options={{ title: 'Edit Profile' }} />
            </Stack.Navigator>
          </ProfileProvider>
        </UserProvider>
      <Toast />
    </NavigationContainer>
    </SafeAreaView>
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

