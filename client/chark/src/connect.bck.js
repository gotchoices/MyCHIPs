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
const headers = {"user-agent": UserAgent, cookie: (Math.random()).toString()}

const ClientAPI = require('wyseman/lib/client_ws')
//var user = 'admin'

const myFetch = function(uri) {
  console.log("Local fetch: ", uri)
  return fetch(uri, {headers})
}
const debug = console.log
//console.log('Crypto:', window.crypto.subtle)

module.exports = class {
  constructor(config) {
    let { webcrypto, listen, wm } = config
    Object.assign(this, {webcrypto, listen, wm})
    this.ws = null
    this.api = new ClientAPI({
      webcrypto: this.webcrypto,
      listen: this.listen,
      fetch: myFetch,
      saveKey: this.saveKey,
      debug:				null //console.log
    })
  }
  
  disconnect() {
    if (!this.ws) return
    this.ws.close()
    this.ws = null
  }

  saveKey(key) {
debug("Save connection key:", typeof key, key)

    const user = key?.user ?? 'user';
    const password = JSON.stringify(key);

    // Store the credentials
    Keychain.setGenericPassword(user, password).catch(err => {
debug("Error saving connection key:", err.message)
    });

    //AsyncStorage.setItem(constants.keyTag, JSON.stringify(key)).catch(err => {
    //})
  }

  /**
   * @callback connectionCallback
   * @param {any} err 
   * @param {boolean} connected 
   */

  /**
   * @param {Object} - Credential object
   * @param {connectionCallback} [cb] - Callback called after connection is established or failed
   */
  credConnect(creds, cb = null) {
    let address = `${creds.host}:${creds.port}`

    if (this.ws) return
    this.api.uri(creds).then(wsURI => {			//Build connection URI	
debug('Connect:', wsURI)
      this.ws = new WebSocket(wsURI, '', {headers})	//Open websocket to backend

      this.ws.onclose = () => this.wm.onClose()
      this.ws.onopen = () => {
        this.wm.onOpen(address, m => {
          this.ws.send(m)
        })
        if(cb) {
          cb(null, true);
        }
      }

      this.ws.onerror = err => {
        if(cb) {
          cb(err);
        }
        this.wm.onClose()
debug("Connection failed:", err.message)
      }
      this.ws.onmessage = e => this.wm.onMessage(e.data)

//      this.wm.register('wylib0', 'wylib.data', (data, err) => {
//debug("Backend supplies wylib data:", !!data, "err:", err)
//      })
    }).catch(err => {
debug('Error initializing', err.message)
      if(cb) {
        cb(err)
      }
    })	// api.uri()
  }
  
  /**
   * @param {Object} ticket - Ticket 
   * @param {connectionCallback} [cb] - Callback called after connection is established or failed
   */
  connect(ticket, cb = null) {
    if (ticket) {
      let creds = Object.assign({}, ticket.ticket)
      //if (!creds.user) creds.user = user
      this.credConnect(creds, (err, connected) => {
        if(cb) {
          cb(err, connected);
        }
      })
    } else {
      Keychain.getGenericPassword().then((credentials) => {
        if(credentials) {
          const val = credentials.password;
          const creds = JSON.parse(val);
          this.credConnect(creds, (err, connected) => {
            if(cb) {
              cb(err, connected)
            }
          })
        } else {
          if(cb) cb(null, false);
        } 
      }).catch(err => {
        debug('Error fetching connection key', err.message)
      })

      //AsyncStorage.getItem(constants.keyTag).then(val => {
        //let creds = JSON.parse(val)
      //})
    }
  }	// connect
}	// class
