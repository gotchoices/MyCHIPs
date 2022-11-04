// Screen to invite another user to tally
// Copyright MyCHIPs.org
// TODO:
//- Display webview
//- Send query to backend when screen launched
//- Create backend function
//- Display QR code received from backend
//- 
import React, { Component, useEffect, useState } from 'react';
import { View, Button, FlatList, Text, StyleSheet } from 'react-native';
import { WebView } from 'react-native-webview';

export default class TallyInvite extends Component {
  constructor(props) {
    super(props)
    this.wm = props.wm
console.log('TI constructor')
//    this.generate()
//    let [data, setData] = useState(null)
     this.data = [
       {name: "One", key: 1},
       {name: "Two", key: 2},
       {name: "Three", key: 3},
     ]
  }

  refresh() {				//Re-load templates from DB
console.log('TI refresh')
    let spec = {
      fields: ['tally_seq', 'contract', 'comment'],
      view: 'mychips.tallies_v_me',
      where: {status: 'draft'}
    }
    this.wm.request('_inv_ref', 'select', spec, data => {
console.log('Template data:', data)
      this.data = data.map(el => ({id: el.tally_seq, contract: el.contract, comment: el.comment}))
    })
  }
  
  generate() {
console.log('TI generate')
    this.wm.request('_invite', 'action', {name:'invite', view:'mychips.tallies_v'}, data => {
console.log('TI data:', data)
    })
  }
  
  render() {return (
    <View style={styles.container}>
      <WebView
        source={{ uri: 'http://gotchoices.org' }}
        style={styles.webView}
      />
      <Button
        title="Regenerate"
        onPress={() => this.generate()}
      />
      <Text>Templates:</Text>
      <FlatList
        data={this.data}
        renderItem={({item}) => <Text style={styles.item}>{item.name}</Text>}
      />
      <Button
        title="Refresh"
        onPress={() => this.refresh()}
      />
    </View>
  )}
}

const styles = StyleSheet.create({
  container: {
    height: 400,
  },
  webView: {
    maxHeight: 360,
    width: 300
  },
  item: {
  },
})
