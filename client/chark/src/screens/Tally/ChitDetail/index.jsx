import React, { useEffect, useMemo, useState } from "react";
import { ActivityIndicator, Alert, ScrollView, StyleSheet, Text, View, RefreshControl } from "react-native";
import { colors, toastVisibilityTime } from "../../../config/constants";
import useSocket from "../../../hooks/useSocket";
import { fetchChitHistory, updateChitState } from "../../../services/tally";
import Button from "../../../components/Button";
import { round } from "../../../utils/common";
import { Toast } from "react-native-toast-message/lib/src/Toast";
import useMessageText from '../../../hooks/useMessageText';
import useTitle from '../../../hooks/useTitle';
import { showError } from '../../../utils/error';
import { useLiftsPayMeText } from '../../../hooks/useLanguage';

const ChitDetail = (props) => {
  const { chit_ent, chit_idx, chit_seq, chit_uuid } = props.route.params;
  const { wm } = useSocket();
  const [chit, setChit] = useState(undefined);
  const [loading, setLoading] = useState(true);

  const { messageText } = useMessageText();
  const chitsMeText = messageText?.chits_v_me?.col;
  const chitsMeMessageText = messageText?.chits_v_me?.msg;
  const charkText = messageText?.chark?.msg;

  const liftsPayMeText = useLiftsPayMeText(wm)

  useTitle(props.navigation, chitsMeMessageText?.detail?.title)

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
        fields: ['net', 'chain_idx', 'signature', 'clean', 'state', 'request', 'status', 'action', 'reference', 'memo'],
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
        setChit(_data);
      }
    }).catch(err => {
      showError(err)
    }).finally(() => setLoading(false))
  }

  const onPay = () => {
    Alert.alert(
      liftsPayMeText?.msg?.accept?.title ?? '',
      charkText?.sure?.help,
      [
        {
          text: charkText?.cancel?.title ?? '',
        },
        {
          text: charkText?.next?.title ?? '',
          onPress: () => {
            updateChitState(
              wm,
              {
                request: 'good',
                chit_uuid
              }
            ).then((data) => {
              Toast.show({
                type: 'success',
                text1: charkText?.updated?.help ?? '',
                visibilityTime: toastVisibilityTime,
              });
              _fetchChitDetails();
            }).catch(err => {
              showError(err);
            });
          }
        },
      ],
      { cancelable: false });
  }


  const onRefuse = () => {
    Alert.alert(
      liftsPayMeText?.msg?.reject?.title ?? '',
      charkText?.sure?.help,
      [
        {
          text: charkText?.cancel?.title ?? '',
        },
        {
          text: charkText?.next?.title ?? '',
          onPress: () => {
            updateChitState(
              wm,
              {
                request: 'void',
                chit_uuid
              }
            ).then((data) => {
              Toast.show({
                type: 'success',
                text1: charkText?.updated?.help ?? '',
                visibilityTime: toastVisibilityTime,
              });
              _fetchChitDetails();
            }).catch(err => {
              showError(err);
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
      <Text style={styles.text}>{chitsMeText?.chit_uuid?.title ?? ''}: {chit_uuid}</Text>
      <Text style={styles.text}>{chitsMeText?.signature?.title ?? ''}: {chit?.signature}</Text>
      <Text style={styles.text}>{chitsMeText?.clean?.title ?? ''}: {chit?.clean?.toString()}</Text>
      <Text style={styles.text}>{chitsMeText?.net?.title ?? ''}: {totalChitNet}</Text>
      <Text style={styles.text}>{chitsMeText?.reference?.title ?? ''}: {JSON.stringify(chit?.reference ?? {})}</Text>
      <Text style={styles.text}>{chitsMeText?.memo?.title ?? ''}: {chit?.memo}</Text>
      <Text style={styles.text}>{chitsMeText?.request?.title ?? ''}: {chit?.request ?? 'None'}</Text>
      <Text style={styles.text}>{chitsMeText?.status?.title ?? ''}: {chit?.status}</Text>
      <Text style={styles.text}>{chitsMeText?.state?.title ?? ''}: {chit?.state}</Text>

    </ScrollView>
    {chit?.action ? <View style={styles.row}>
      <Button
        title="Refuse"
        onPress={onRefuse}
        style={styles.refuse}
      />

      <Button
        title={charkText?.edit?.title ?? ''}
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
