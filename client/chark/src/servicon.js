// Display status of connection with backend server
// Copyright MyCHIPs.org
// TODO:
//X- Make it display connection status
//- Embelish with icons/styles
//- Clicking on it will toggle connection status (is this needed?)
//- 
import React, { useState } from 'react';
import { View, Text, StyleSheet, Image, Button, TouchableWithoutFeedback } from 'react-native';

import useSocket from './hooks/useSocket';

import CenteredModal from './components/CenteredModal';
import TokenDebug from './components/TokenDebug';

const ServIcon = () => {
  const { status } = useSocket();
  const [isModalVisible, setIsModalVisible] = useState(false);

  const onCancel = () => {
    setIsModalVisible(false);
  }

  return (
    <>
      <View>
        <TouchableWithoutFeedback
          onPress={() => setIsModalVisible(true)}
        >
          <Text style={{ paddingLeft: 14, paddingVertical: 5 }}>
            {status}
          </Text>
        </TouchableWithoutFeedback>
      </View>

      <CenteredModal
        isVisible={isModalVisible}
        onClose={onCancel}
      >
        <TokenDebug 
          onCancel={onCancel}
        />
      </CenteredModal>
    </>
  )
}

  /*
export default class ServIcon extends Component {
  constructor(props) {
    super(props)
    this.state = {server: null}

    props.wm.request('_main', 'connect', {stay: true}, addr => {
console.log('Connection address:', addr)
      this.setState({server: addr})
    })
  }

  render() {return (
    <View>
      <Text>Server:{this.props.connecting ? ' Connecting...' : this.state.server}</Text>
    </View>
  )}
}
*/

//const styles = StyleSheet.create({
//  buttonBox: {
//    alignItems: 'center',
//    backgroundColor: '#e0e0e0',
//    borderRadius: 8,
//    flex: 1,
//  },
//})
//

export default ServIcon;
