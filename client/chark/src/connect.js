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
import AsyncStorage from '@react-native-async-storage/async-storage'

import constants from './config/constants';

const ClientAPI = require('wyseman/lib/client_ws')
var user = 'admin'

const myFetch = function(uri, options) {
  console.log("Local fetch")
  return fetch(uri, options)
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
    AsyncStorage.setItem(constants.keyTag, JSON.stringify(key)).catch(err => {
debug("Error saving connection key:", err.message)
    })
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
console.log('Pre:', creds)
    if (this.ws) return
    this.api.uri(creds).then(wsURI => {			//Build connection URI	
debug('Connect:', wsURI)
      this.ws = new WebSocket(wsURI)			//Open websocket to backend

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
    })	// api.uri()
  }
  
  /**
   * @param {Object} ticket - Ticket 
   * @param {connectionCallback} [cb] - Callback called after connection is established or failed
   */
  connect(ticket, cb = null) {
    if (ticket) {
      let creds = Object.assign({}, ticket.ticket)
      if (!creds.user) creds.user = user
      this.credConnect(creds, (err, connected) => {
        if(cb) {
          cb(err, connected);
        }
      })
    } else {
      AsyncStorage.getItem(constants.keyTag).then(val => {
        let creds = JSON.parse(val)
        this.credConnect(creds)
      }).catch(err => {
debug('Error fetching connection key', err.message)
      })
    }
  }	// connect
}	// class
