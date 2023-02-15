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
import { createBottomTabNavigator } from '@react-navigation/bottom-tabs';
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
import SocketProvider from './src/components/SocketProvider';

const listen = ['mychips_user','wylib']		//Listen for these notifies from the DB

const HomeStack = createNativeStackNavigator();
function HomeStackScreen() {
  return (
    <HomeStack.Navigator>
      <HomeStack.Screen name="Home" component={Home} options={{ headerShown: false }} />
      <HomeStack.Screen name="TallyReport" component={TallyReport} />
      <HomeStack.Screen name="OpenTallyEdit" component={EditOpenTally} options={{ title: 'Open Tally' }} />
      <HomeStack.Screen name="TallyAccept" component={TallyAccept} options={{ title: 'Tally Accept' }} />
    </HomeStack.Navigator>
  );
}

function ReceiveScreen({ navigation }) {
  return (
    <View style={{ flex: 1, alignItems: 'center', justifyContent: 'center' }}>
      <Text>Receive Screen</Text>
    </View>
  );
}

const InviteStack = createNativeStackNavigator();
function InviteStackScreen() {
  return (
    <InviteStack.Navigator>
      <InviteStack.Screen name="Invite" component={Invite} options={{ headerShown: false }} />
      <InviteStack.Screen name="TallyEdit" component={EditDraftTally} options={{ title: 'Draft Tally' }}  />
    </InviteStack.Navigator>
  );
}

const SettingStack = createNativeStackNavigator();
function SettingStackScreen() {
  return (
    <SettingStack.Navigator>
      <SettingStack.Screen name="Setting" component={Setting} />
      <SettingStack.Screen name="Profile" component={Profile} options={{ title: 'Profile' }} />
      <SettingStack.Screen name="ProfileEdit" component={ProfileEdit} options={{ title: 'Edit Profile' }} />
    </SettingStack.Navigator>
  );
}

const Tab = createBottomTabNavigator();
const Stack = createNativeStackNavigator();
const linking = {
  prefixes: ["mychips://", "https://mychips.org"],
  config: {
    screens:{
      Tally: {
        screens: {
          Home: {
            path: 'connect',
          },
          TallyAccept: {
            path: 'tally-accept',
          }
        }
      },
    },
  },
};  

function App() {
  return (
    <SafeAreaView style={{ flex: 1 }}>
      <NavigationContainer linking={linking}>
        <UserProvider>
          <SocketProvider>
            <ServIcon />
            <PolyfillCrypto />
              <ProfileProvider>
                <Tab.Navigator screenOptions={{ headerShown: false, tabBarShowLabel: false }}>
                  <Tab.Screen
                    name="Tally"
                    component={HomeStackScreen}
                    options={{
                      tabBarIcon: () => (
                        <Image style={styles.button} source={require("./assets/icon-home.png")}/>
                      )
                    }}
                  />

                  <Tab.Screen
                    name="Receive"
                    component={ReceiveScreen}
                    options={{
                      tabBarIcon: () => (
                        <Image style={styles.button} source={require("./assets/icon-receive.png")}/>
                      )
                    }}
                  />

                  <Tab.Screen
                    name="Scan"
                    component={Scanner}
                    options={{
                      unmountOnBlur: true,
                      tabBarIcon: () => (
                        <Image style={styles.button} source={require("./assets/icon-scan.png")}/>
                      )
                    }}
                  />

                  <Tab.Screen
                    name="Invite Screen"
                    component={InviteStackScreen}
                    options={{
                      tabBarIcon: () => (
                        <Image style={styles.button} source={require("./assets/icon-invite.png")}/>
                      )
                    }}
                  />

                  <Tab.Screen
                    name="Settings"
                    component={SettingStackScreen}
                    options={{
                      tabBarIcon: () => (
                        <Image style={styles.button} source={require("./assets/icon-settings.png")}/>
                      )
                    }}
                  />
                </Tab.Navigator>
              </ProfileProvider>
            <Toast />
          </SocketProvider>
        </UserProvider>
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

