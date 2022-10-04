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

const ClientAPI = require('wyseman/lib/client_ws')
const keyTag = 'connectKey'
var user = 'admin'

const myFetch = function(uri, options) {
  console.log("Local fetch")
  return fetch(uri, options)
}
const debug = console.log
//console.log('Crypto:', window.crypto.subtle)

module.exports = class {
  constructor(config) {
    let { webcrypto, httpPort, wsPort, listen, wm } = config
    Object.assign(this, {webcrypto, httpPort, wsPort, listen, wm})
    this.ws = null
    this.api = new ClientAPI({
      webcrypto: this.webcrypto,
      listen: this.listen,
      httpPort: this.httpPort,
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
    AsyncStorage.setItem(keyTag, JSON.stringify(key)).catch(err => {
debug("Error saving connection key:", err.message)
    })
  }

  credConnect(creds) {
    let address = `${creds.host}:${this.wsPort}`
console.log('Pre:', creds)
    if (this.ws) return
    this.api.uri(creds).then(wsURI => {			//Build connection URI	
debug('Connect:', wsURI)
      this.ws = new WebSocket(wsURI)			//Open websocket to backend

      this.ws.onclose = () => this.wm.onClose()
      this.ws.onopen = () => this.wm.onOpen(address, m => {
        this.ws.send(m)
      })
      this.ws.onerror = err => {
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
  
  connect(ticket) {
    if (ticket) {
      let creds = Object.assign({user}, ticket.ticket)
      this.credConnect(creds)
    } else {
      AsyncStorage.getItem(keyTag).then(val => {
        let creds = JSON.parse(val)
        this.credConnect(creds)
      }).catch(err => {
debug('Error fetching connection key', err.message)
      })
    }
  }	// connect
}	// class
