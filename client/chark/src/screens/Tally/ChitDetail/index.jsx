import React, { useEffect, useMemo, useState } from "react";
import { ActivityIndicator, Alert, ScrollView, StyleSheet, Text, View, RefreshControl } from "react-native";
import { colors } from "../../../config/constants";
import useSocket from "../../../hooks/useSocket";
import { fetchChitHistory, updateChitRequest } from "../../../services/tally";
import Button from "../../../components/Button";
import { round } from "../../../utils/common";
import { Toast } from "react-native-toast-message/lib/src/Toast";

const ChitDetail = (props) => {
  const { chit_ent, chit_idx, chit_seq, chit_uuid } = props.route.params;
  const { wm } = useSocket();
  const [chit, setChit] = useState(undefined);
  const [loading, setLoading] = useState(true);

  const totalChitNet = useMemo(() => {
    const net = chit?.net;
    if (net) {
      return round(net / 1000, 3)
    }
    return 0;
  }, [chit?.net]);

  useEffect(() => {
    if (chit_uuid) {
      _fetchChitDetails();
    }
  }, [chit_uuid])

  const _fetchChitDetails = () => {
    fetchChitHistory(
      wm,
      {
        fields: ['net', 'chain_idx', 'chain_hash', 'signature', 'clean', 'state', 'request', 'status', 'action', 'reference', 'memo'],
        where: {
          chit_uuid,
          chit_ent,
          chit_idx,
          chit_seq,
        },
      }
    ).then(data => {
      if (data.length > 0) {
        const _data = data[0];
        console.log("CHIT_DETAIL_CONTENT ==> ", JSON.stringify(_data));
        setChit(_data);
      }
    }).catch(ex => {
      Alert.alert("Error", ex);
    }).finally(() => setLoading(false))
  }

  const onPay = () => {
    Alert.alert(
      "Confirmn Payment",
      "Are you sure to confir payment?",
      [
        {
          text: 'Cancel'
        },
        {
          text: 'Ok',
          onPress: () => {
            updateChitRequest(
              wm,
              {
                request: 'good',
                chit_uuid
              }
            ).then((data) => {
              console.log("ACCEPT RESPONSE ==> ", JSON.stringify(data));
              Toast.show({ type: 'success', text1: 'Chit request accepted successfully' });
              _fetchChitDetails();
            }).catch(ex => {
              console.log("ERROR ==> ", ex);
              Toast.show({ type: 'error', text1: 'Failed to accept chit request please try again' });
            });
          }
        },
      ],
      { cancelable: false });
  }


  const onRefuse = () => {
    Alert.alert(
      "Refuse Payment",
      "Are you sure to refuse payment request?",
      [
        {
          text: "Cancel",
        },
        {
          text: 'Yes',
          onPress: () => {
            updateChitRequest(
              wm,
              {
                request: 'void',
                chit_uuid
              }
            ).then((data) => {
              console.log("REFUSE RESPONSE ==> ", JSON.stringify(data));
              Toast.show({ type: 'success', text1: 'Chit request refused successfully' });
              _fetchChitDetails();
            }).catch(ex => {
              console.log("ERROR ==> ", ex);
              Toast.show({ type: 'error', text1: 'Failed to refuse chit please try again.' })
            });
          }
        }
      ],
      { cancelable: false }
    )
  }

  const onEdit = () => {
    props.navigation.navigate("RequestDetail", {
      editDetails: {
        chit_ent: chit_ent,
        chit_idx: chit_idx,
        chit_seq: chit_seq,
        chit_uuid: chit_uuid,
        memo: chit?.memo,
        reference: chit?.reference,
        net: totalChitNet,
      }
    });
  }

  if (loading) {
    return <View style={styles.loadingContainer}>
      <ActivityIndicator />
    </View>
  }

  return <View style={styles.container}>
    <ScrollView
      style={styles.container}
      contentContainerStyle={styles.contentContainer}
      refreshControl={
        <RefreshControl
          refreshing={loading}
          onRefresh={_fetchChitDetails}
        />
      }
    >
      <Text style={styles.text}>CHIT UUID: {chit_uuid}</Text>
      <Text style={styles.text}>CHAIN HASH: {chit?.chain_hash?.type} {chit?.chain_hash?.data?.toString()}</Text>
      <Text style={styles.text}>SIGNATURE: {chit?.signature}</Text>
      <Text style={styles.text}>CLEAN: {chit?.clean?.toString()}</Text>
      <Text style={styles.text}>NET: {totalChitNet}</Text>
      <Text style={styles.text}>REFERENCE: {chit?.reference}</Text>
      <Text style={styles.text}>MEMO: {chit?.memo}</Text>
      <Text style={styles.text}>REQUEST: {chit?.request ?? 'None'}</Text>
      <Text style={styles.text}>STATUS: {chit?.status}</Text>
      <Text style={styles.text}>STATE: {chit?.state}</Text>
      <Text style={styles.text}>ACTION: {chit?.action?.toString() ?? 'None'}</Text>

    </ScrollView>
    {chit?.action ? <View style={styles.row}>
      <Button
        title="Refuse"
        onPress={onRefuse}
        style={styles.refuse}
      />

      <Button
        title="Modify"
        onPress={onEdit}
        style={styles.edit}
      />

      <Button
        title="Pay"
        onPress={onPay}
        style={styles.pay}
      />
    </View> : <></>
    }
  </View>
}


const styles = StyleSheet.create({
  container: { flex: 1 },
  contentContainer: {
    backgroundColor: colors.white,
    padding: 16,
    margin: 12,
  },
  text: {
    fontSize: 16,
    color: colors.black,
    marginVertical: 8,
  },
  loadingContainer: {
    flex: 1,
    justifyContent: 'center',
    alignItems: 'center',
  },
  row: {
    flexDirection: 'row',
    justifyContent: 'flex-start',
    alignItems: 'center',
    padding: 16,
    backgroundColor: colors.white,
    margin: 12,
  },
  pay: {
    borderRadius: 8,
    paddingHorizontal: 24,
    marginStart: 16,
    backgroundColor: 'green',
    borderColor: 'green',
  },
  refuse: {
    backgroundColor: colors.red,
    borderColor: colors.red,
    borderRadius: 8,
    paddingHorizontal: 16,
  },
  edit: {
    marginStart: 16,
    borderRadius: 8,
    paddingHorizontal: 16,
  }
})
export default ChitDetail;