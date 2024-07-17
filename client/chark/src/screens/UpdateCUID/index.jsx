import React, { useState } from "react";
import { StyleSheet, TextInput, View, Text, Alert } from "react-native";
import { colors, toastVisibilityTime } from "../../config/constants";
import Button from "../../components/Button";
import { updateCUID } from "../../services/profile";
import useSocket from "../../hooks/useSocket";
import { Toast } from "react-native-toast-message/lib/src/Toast";
import useMessageText from '../../hooks/useMessageText';
import CustomToast from '../../components/Toast';

const UpdateCUID = (props) => {
  const { wm } = useSocket();
  const [cuid, setCuid] = useState()
  const [disabled, setDdisabled] = useState(false);
  const { messageText } = useMessageText();
  const charkText = messageText?.chark?.msg;

  const onUpdate = () => {
    if (!cuid) {
      return Toast.show({
        type: 'error',
        text1: 'Enter CUID to continue',
        visibilityTime: toastVisibilityTime,
      })
    }
    setDdisabled(true);
    updateCUID(
      wm,
      {
        peer_cuid: cuid.toString(),
        where: {
          user_ent: props.userId
        }
      }
    ).then(data => {
      Toast.show({
        type: 'success',
        text1: charkText?.updated?.help ?? '',
        visibilityTime: toastVisibilityTime,
      });
      props.success(cuid.toString());

    }).catch(ex => {
      console.log("ERROR ==> ", ex);
      Alert.alert("Error", ex.toString());
    }).finally(() => {
      setDdisabled(false);
    })
  }

  return <View style={styles.container}>
    <View style={styles.header}>
      <Text style={styles.title}>Please Set Your User ID </Text>
    </View>
    <TextInput
      style={styles.textInput}
      placeholder=""
      value={cuid}
      onChangeText={setCuid}
    />
    <View style={styles.row}>
      <Button
        onPress={props.cancel}
        title={charkText?.cancel?.title ?? ''}
        style={styles.button}
        disabled={disabled}
      />
      <View style={{ width: 12 }} />
      <Button
        onPress={onUpdate}
        title={charkText?.save?.title ?? ''}
        style={styles.button}
        disabled={disabled}
      />
    </View>
    <CustomToast />
  </View>
}


const styles = StyleSheet.create({
  container: {
    flex: 1,
    width: '100%',
    alignItems: 'center',
  },
  title: {
    fontSize: 18,
    marginBottom: 8,
    fontWeight: 'bold',
    fontWeight: '400',
    fontFamily: 'inter',
    color: colors.black,
  },
  textInput: {
    width: '90%',
    marginVertical: 24,
    borderWidth: 1,
    padding: 10,
    borderColor: colors.dimgray,
  },
  row: {
    flexDirection: 'row'
  },
  header: {
    width: '100%',
    padding: 10,
    marginBottom: 10,
    borderBottomWidth: 1,
    borderBottomColor: colors.lightgray,
  },
  button: {
    borderRadius: 40,
    paddingHorizontal: 20,
  }
})

export default UpdateCUID;
