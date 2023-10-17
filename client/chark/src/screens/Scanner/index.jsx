import React, { useState, useEffect } from 'react'
import { StyleSheet, Text, ActivityIndicator, Modal, View, Button, TextInput, Alert } from 'react-native';
import { useCameraDevices, Camera } from 'react-native-vision-camera';
import { useScanBarcodes, BarcodeFormat } from 'vision-camera-code-scanner';
import * as Keychain from 'react-native-keychain';

import { colors, qrType } from '../../config/constants';
import useSocket from '../../hooks/useSocket';
import { parse } from '../../utils/query-string';

const connectionLink = 'https://mychips.org/ticket'

const Scanner = (props) => {
  const devices = useCameraDevices();
  const device = devices.back;
  const { connectSocket, disconnectSocket, wm, ws } = useSocket();

  const [hasPermission, setHasPermission] = useState(false);
  const [isActive, setIsActive] = useState(true);
  const [isConnecting, setIsConnecting] = useState(false);
  const [isModalVisible, setIsModalVisible] = useState(false);
  const [username, setUsername] = useState('');
  const [usernameError, setUsernameError] = useState();

  // Temporary storage for qr code if username is not included in the ticket
  const [tempQrCode, setTempQrCode] = useState();

  const [frameProcessor, barcodes] = useScanBarcodes([BarcodeFormat.QR_CODE], {
    checkInverted: true,
  });

  const qrCode = barcodes?.[0]?.displayValue;

  useEffect(() => {
    if(qrCode) {
      if(qrCode.startsWith(connectionLink)) {
        const obj = parse(qrCode);
        connect({ connect: obj });
      } else {
        try {
          setIsActive(false);
          const parsedCode = JSON.parse(qrCode);
          console.log("PARSED_CODE ==> ", parsedCode);
          if(parsedCode?.invite) {
            requestTally(parsedCode);
          } else if (parsedCode?.signkey) {
            props.navigation.navigate("Settings", {screen: "ImportKey", params: parsedCode});
          } else {
            processConnect(parsedCode);
          }
        } catch(err) {
          console.log(err.message)
        }
      }


    }

    // Request Tally
    function requestTally(parsed) {
      props.navigation.navigate('Home', parsed);
    }

    // Process the connection
    function processConnect(parsed) {
      if(parsed?.connect && parsed?.connect?.user) {
        connect({ connect: parsed.connect})
      } else if(parsed?.connect) {
        setTempQrCode(parsed.connect);
        setIsModalVisible(true);
      }
    }

  }, [qrCode, setIsActive])

  /**
   * @param {Object} args
   * @param {Object} args.ticket
   * @param {string} [args.username]
   * @param {boolean} [args.needUsername]
  */
  const connect = (args) => {
    console.log(args, 'args')
    let ticket = args?.connect;
    const username = args?.username?.trim();

    if(!ticket) {
      return Alert.alert('Ticket not found.');
    }

    if(args.needUsername === true && !username) {
      setUsernameError('Username required');
      return;
    }
    setIsConnecting(true);
    setIsModalVisible(false);

    if(username) {
      ticket.user = username;
    }

    connectSocket({
      ticket,
    }, (err, connected) => {
      if(err) {
        setIsActive(true);
        setIsConnecting(false);
        Keychain.resetGenericPassword();
        disconnectSocket();

        Alert.alert(err.message);
      } else if (connected){
        setIsConnecting(false);
        props.navigation.navigate('Home');
      }

      setUsername(false);
    });
  }

  useEffect(() => {
    Camera.requestCameraPermission()
      .then(status => {
        setHasPermission(status === 'authorized');
      })
  }, []);

  return (
    device && hasPermission && (
      <View style={{ flex: 1, alignItems: 'center', justifyContent: 'center' }}>
        <Camera
          style={StyleSheet.absoluteFill}
          device={device}
          isActive={isActive}
          frameProcessor={frameProcessor}
          frameProcessorFps={5}
        />
        {
          isConnecting && (
            <>
              <ActivityIndicator size="large" color="#fff" />
              <Text style={styles.connectingText}>
                Connecting...
              </Text>
            </>
          )
        }

        <Modal
          animationType="slide"
          transparent={true}
          visible={isModalVisible}
          onRequestClose={() => {
            setIsModalVisible(false);
          }}
        >
          <View style={styles.centeredView}>
            <View style={styles.modalView}>
              <View style={styles.formControl}>
                <Text style={{ fontWeight: 'bold', marginBottom: 10 }}>Username</Text>
                <TextInput
                  style={styles.input}
                  placeholder="Enter username"
                  onChangeText={setUsername}
                />

                {
                  usernameError && <Text style={{ color: colors.red }}>{usernameError}</Text>
                }
              </View>

              <Button
                title="Connect"
                onPress={() => connect({
                  ticket: tempQrCode,
                  username,
                  needUsername: true,
                })}
              />
            </View>
          </View>
        </Modal>
      </View>
    )
  );
}

const styles = StyleSheet.create({
  connectingText: {
    fontSize: 20,
    color: 'white',
    fontWeight: 'bold',
  },
  centeredView: {
    flex: 1,
    justifyContent: "center",
    alignItems: "center",
    marginTop: 22,
  },
  modalView: {
    width: '80%',
    margin: 20,
    backgroundColor: "white",
    borderRadius: 20,
    padding: 35,
    shadowColor: "#000",
    shadowOffset: {
      width: 0,
      height: 2
    },
    shadowOpacity: 0.25,
    shadowRadius: 4,
    elevation: 5
  },
  button: {
    borderRadius: 20,
    padding: 10,
    elevation: 2
  },
  formControl: {
    marginVertical: 10,
  },
  input: {
    padding: 10,
    backgroundColor: colors.gray100,
  },
});

export default Scanner;
