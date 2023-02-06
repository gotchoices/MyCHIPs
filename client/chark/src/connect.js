// Manage connection to the backend
// Copyright MyCHIPs.org
// TODO:
//X- Can be called with ticket
//X- Can reconnect using stored key
//- Store connection key securely
//- Use pass-phrase or biometrics to unlock stored key
//- Display errors to user (how/where)
//- Prompt user for their username if not present in creds already
//- Can detect if/when connection dropped
//- Re-establish connection as needed
//- 

//import React, { Component } from 'react'
//import { Button, View, Text, StyleSheet, TouchableOpacity, Image, NativeModules } from 'react-native'
import * as Keychain from 'react-native-keychain';

import constants from './config/constants';
const UserAgent = "MyCHIPs Chark Client"
export const headers = {"user-agent": UserAgent, cookie: (Math.random()).toString()}

const ClientAPI = require('wyseman/lib/client_ws')

const myFetch = function(uri) {
  console.log("Local fetch: ", uri)
  return fetch(uri, {headers})
}

export default class Connect {
  constructor(config) {
    let { webcrypto, listen, wm } = config

    this.api = new ClientAPI({
      listen,
      webcrypto,
      debug: null,
      fetch: myFetch,
      saveKey: this.saveKey,
    });
  }

  saveKey = (key) => {
    console.log("Save connection key:", typeof key, key)

    const user = key?.user ?? 'user';
    const password = JSON.stringify(key);

    // Store the credentials
    Keychain.setGenericPassword(user, password).catch(err => {
      console.log("Error saving connection key:", err.message)
    });
  }

  getUrl = (creds) => {
    let address = `${creds.host}:${creds.port}`

    return this.api.uri(creds)
  }

}

