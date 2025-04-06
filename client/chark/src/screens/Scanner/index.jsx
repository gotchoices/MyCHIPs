import React, {useState, useEffect} from 'react';
import {
  StyleSheet,
  Text,
  ActivityIndicator,
  Modal,
  View,
  Button,
  TextInput,
  Alert,
  Platform,
} from 'react-native';
import ScannerCamera from '../../utils/scanner';
import * as Keychain from 'react-native-keychain';
import {colors} from '../../config/constants';
import useSocket from '../../hooks/useSocket';
import {parse} from '../../utils/query-string';
import {PERMISSIONS, RESULTS, check, request} from 'react-native-permissions';
import {LINK_PREFIXES, addUuidToUrl} from '../../utils/deep-links';

const Scanner = props => {
  const {connectSocket, disconnectSocket, status} = useSocket();

  const [hasPermission, setHasPermission] = useState(false);
  const [isActive, setIsActive] = useState(true);
  const [isConnecting, setIsConnecting] = useState(false);
  const [isModalVisible, setIsModalVisible] = useState(false);
  const [username, setUsername] = useState('');
  const [usernameError, setUsernameError] = useState();

  // Temporary storage for qr code if username is not included in the ticket
  const [tempQrCode, setTempQrCode] = useState();

  const connectionStatus = {
    connected: 'Connected',
    disconnect: 'Disconnected',
    connecting: 'Connecting',
  };

  const showAlert = obj => {
    Alert.alert(
      'New Ticket found',
      'Do you want to connect to a new connect ticket?',
      [
        {text: 'Cancel'},
        {text: 'Continue', onPress: () => connect({connect: obj})},
      ],
    );
  };

  const onQrAccepted = event => {
    const qrCode = event.nativeEvent.codeStringValue;
    if (qrCode) {
      setIsActive(false);
      if (qrCode.startsWith(LINK_PREFIXES.TICKET)) {
        const obj = parse(qrCode);
        
        // Always show confirmation alert before connecting, regardless of current connection status
        showAlert(obj);
        
        // Previous code had two different paths:
        // if (status !== connectionStatus.disconnect) {
        //   showAlert(obj);  // Show alert only if already connected
        // } else {
        //   connect({connect: obj});  // Connect immediately if disconnected
        // }
      } else if (qrCode.startsWith(LINK_PREFIXES.PAY)) {
        /**
         * Using randomString to re-excute the requestPay function
         * such that if scanned same url can make the payment again
         */
        const payUrl = addUuidToUrl(qrCode);
        requestPay(payUrl);
      } else if (qrCode.startsWith(LINK_PREFIXES.INVITE)) {
        /**
         * Using randomString to re-excute the tally share function
         * such that if scanned same url can scan the tally request
         */
        const tallyInviteUrl = addUuidToUrl(qrCode);
        requestTally(tallyInviteUrl);
      } else if (qrCode.startsWith(LINK_PREFIXES.SIGNKEY)) {
        /**
         * Using randomString to re-execute the signkey import function
         * such that if scanned same url can be processed again
         */
        const signkeyUrl = addUuidToUrl(qrCode);
        
        props.navigation.navigate('Settings', {
          screen: 'KeyManagement',
          params: {
            signkeyUrl: signkeyUrl,
            autoImport: true
          }
        });
      } else {
        try {
          setIsActive(false);
          const parsedCode = JSON.parse(qrCode);

          console.log('PARSED_CODE ==> ', parsedCode);
          if (parsedCode?.signkey) {
            // Handle JSON signkey format
            props.navigation.navigate('Settings', {
              screen: 'KeyManagement',
              params: {
                jsonData: parsedCode,
                autoImport: true
              }
            });
          } else {
            processConnect(parsedCode);
          }
        } catch (err) {
          console.log(err.message);
        }
      }
    }
  };

  // Request Tally
  function requestTally(tallyInviteUrl) {
    props.navigation.navigate('Home', {tallyInviteUrl});
  }

  // Request pay
  function requestPay(payUrl) {
    props.navigation.navigate('Home', {payUrl});
  }

  // Process the connection
  function processConnect(parsed) {
    if (parsed?.connect && parsed?.connect?.user) {
      // Show confirmation alert instead of connecting immediately
      showAlert(parsed.connect);
      // Previous code directly connected:
      // connect({connect: parsed.connect});
    } else if (parsed?.connect) {
      // Username not included, show the username input modal
      setTempQrCode(parsed.connect);
      setIsModalVisible(true);
    }
  }

  /**
   * @param {Object} args
   * @param {Object} args.ticket
   * @param {string} [args.username]
   * @param {boolean} [args.needUsername]
   */
  const connect = args => {
    let ticket = args?.connect;
    const username = args?.username?.trim();

    if (!ticket) {
      setIsActive(true);
      return Alert.alert('Ticket not found.');
    }

    if (args.needUsername === true && !username) {
      setUsernameError('Username required');
      return;
    }
    setIsConnecting(true);
    setIsModalVisible(false);

    if (username) {
      ticket.user = username;
    }

    connectSocket(
      {
        ticket,
      },
      (err, connected) => {
        if (err) {
          setIsConnecting(false);
          // Previous code was deleting the key on error - removed:
          // Keychain.resetGenericPassword();
          disconnectSocket();

          Alert.alert(err.message);

          setTimeout(() => setIsActive(true), 1000);
        } else if (connected) {
          // Connection successful - existing key was already reset in connectSocket()
          setIsConnecting(false);
          props.navigation.navigate('Home');
        }

        setUsername(false);
      },
    );
  };

  const requestCameraPermission = () => {
    const permission =
      Platform.OS === 'ios'
        ? PERMISSIONS.IOS.CAMERA
        : PERMISSIONS.ANDROID.CAMERA;

    return check(permission).then(status => {
      if (status === RESULTS.GRANTED || status === RESULTS.LIMITED) {
        return setHasPermission(true);
      }

      request(permission).then(status => {
        if (status === RESULTS.GRANTED || status === RESULTS.LIMITED) {
          return setHasPermission(true);
        }
      });
    });
  };

  useEffect(() => {
    requestCameraPermission();
  }, []);

  return (
    hasPermission && (
      <View style={{flex: 1, alignItems: 'center', justifyContent: 'center'}}>
        {isActive ? (
          <ScannerCamera
            style={StyleSheet.absoluteFill}
            isActive={isActive}
            onReadCode={onQrAccepted}
          />
        ) : (
          <ScannerCamera
            style={StyleSheet.absoluteFill}
            isActive={false}
            onReadCode={onQrAccepted}
          />
        )}

        {isConnecting && (
          <>
            <ActivityIndicator size="large" color="#fff" />
            <Text style={styles.connectingText}>Connecting...</Text>
          </>
        )}

        <Modal
          animationType="slide"
          transparent={true}
          visible={isModalVisible}
          onRequestClose={() => {
            setIsModalVisible(false);
          }}>
          <View style={styles.centeredView}>
            <View style={styles.modalView}>
              <View style={styles.formControl}>
                <Text style={{fontWeight: 'bold', marginBottom: 10}}>
                  Username
                </Text>
                <TextInput
                  style={styles.input}
                  placeholder="Enter username"
                  onChangeText={setUsername}
                />

                {usernameError && (
                  <Text style={{color: colors.red}}>{usernameError}</Text>
                )}
              </View>

              <Button
                title="Connect"
                onPress={() =>
                  connect({
                    ticket: tempQrCode,
                    username,
                    needUsername: true,
                  })
                }
              />
            </View>
          </View>
        </Modal>
      </View>
    )
  );
};

const styles = StyleSheet.create({
  connectingText: {
    fontSize: 20,
    color: 'white',
    fontWeight: 'bold',
  },
  centeredView: {
    flex: 1,
    justifyContent: 'center',
    alignItems: 'center',
    marginTop: 22,
  },
  modalView: {
    width: '80%',
    margin: 20,
    backgroundColor: 'white',
    borderRadius: 20,
    padding: 35,
    shadowColor: '#000',
    shadowOffset: {
      width: 0,
      height: 2,
    },
    shadowOpacity: 0.25,
    shadowRadius: 4,
    elevation: 5,
  },
  button: {
    borderRadius: 20,
    padding: 10,
    elevation: 2,
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
