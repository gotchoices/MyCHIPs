import React, { useState } from "react";
import { StyleSheet, TextInput, View, Text, Alert } from "react-native";
import { colors, toastVisibilityTime } from "../../config/constants";
import Button from "../../components/Button";
import { updateCID } from "../../services/profile";
import useSocket from "../../hooks/useSocket";
import { Toast } from "react-native-toast-message/lib/src/Toast";
import useMessageText from '../../hooks/useMessageText';

const UpdateCID = (props) => {
  const { wm } = useSocket();
  const [cid, setCid] = useState()
  const [disabled, setDdisabled] = useState(false);
  const { messageText } = useMessageText();
  const charkText = messageText?.chark?.msg;

  const onUpdate = () => {
    if (!cid) {
      Alert.alert("Error", "Enter CID to continue");
      return;
    }
    setDdisabled(true);
    updateCID(
      wm,
      {
        peer_cid: cid.toString(),
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
      props.success(cid.toString());

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
      placeholder="Eg. name_lastname"
      value={cid}
      onChangeText={setCid}
    />
    <View style={styles.row}>
      <Button
        onPress={props.cancel}
        title="Cancel"
        style={styles.button}
        disabled={disabled}
      />
      <View style={{ width: 12 }} />
      <Button
        onPress={onUpdate}
        title="Update CID"
        style={styles.button}
        disabled={disabled}
      />
    </View>
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
    fontWeight: 'bold',
  },
  textInput: {
    width: '90%',
    marginVertical: 24,
    borderWidth: 1,
    padding: 10,
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
    paddingHorizontal: 20,
  }
})

export default UpdateCID;
