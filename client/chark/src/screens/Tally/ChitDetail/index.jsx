import React, { useEffect, useState } from "react";
import { ActivityIndicator, Alert, ScrollView, StyleSheet, Text, View, RefreshControl, TouchableOpacity } from "react-native";
import { colors, toastVisibilityTime } from "../../../config/constants";
import useSocket from "../../../hooks/useSocket";
import { fetchChitHistory, fetchTallies, updateChitState } from "../../../services/tally";
import Button from "../../../components/Button";
import ChipValue from "../../../components/ChipValue";
import { Toast } from "react-native-toast-message/lib/src/Toast";
import useMessageText from '../../../hooks/useMessageText';
import useTitle from '../../../hooks/useTitle';
import { showError } from '../../../utils/error';
import { useLiftsPayMeText } from '../../../hooks/useLanguage';
import { useSelector } from "react-redux";

const ChitDetail = (props) => {
  const { chit_ent, chit_idx, chit_seq, chit_uuid } = props.route.params;
  const { wm } = useSocket();
  const [chit, setChit] = useState(undefined);
  const [loading, setLoading] = useState(true);
  const [tallyDetails, setTallyDetails] = useState(null);
  const [loadingTally, setLoadingTally] = useState(false);

  // Get open tallies data from Redux to find partner name
  const { tallies: openTallies } = useSelector(state => state.openTallies);

  const { messageText } = useMessageText();
  const chitsMeText = messageText?.chits_v_me?.col;
  const chitsMeMessageText = messageText?.chits_v_me?.msg;
  const talliesMeText = messageText?.tallies_v_me?.col;
  const charkText = messageText?.chark?.msg;

  const liftsPayMeText = useLiftsPayMeText(wm)

  useTitle(props.navigation, chitsMeMessageText?.detail?.title)

  // We no longer need totalChitNet since we'll use the ChipValue component directly

  // Function to extract partner name from a tally
  const getPartnerName = (tally) => {
    if (!tally?.part_cert) return "";
    
    const partCert = tally.part_cert;
    return partCert.type === 'o'
      ? `${partCert.name}`
      : `${partCert?.name?.first || ''}${partCert?.name?.middle ? ' ' + partCert?.name?.middle : ''} ${partCert?.name?.surname || ''}`.trim();
  }

  // Get the tally details, first from Redux, then from direct fetch if needed
  useEffect(() => {
    if (chit && chit.tally_uuid) {
      // First try to find in Redux state
      const tally = openTallies.find(t => t.tally_uuid === chit.tally_uuid);
      if (tally) {
        setTallyDetails(tally);
        return;
      }
      
      // If not found in Redux, fetch directly
      setLoadingTally(true);
      fetchTallies(wm, {
        fields: ['tally_ent', 'tally_seq', 'tally_uuid', 'part_cert', 'tally_type'],
        where: {
          tally_uuid: chit.tally_uuid
        }
      })
      .then(tallies => {
        if (tallies && tallies.length > 0) {
          setTallyDetails(tallies[0]);
        }
      })
      .catch(err => {
        console.log("Error fetching tally details:", err);
      })
      .finally(() => {
        setLoadingTally(false);
      });
    }
  }, [chit?.tally_uuid, openTallies]);

  useEffect(() => {
    if (chit_uuid) {
      _fetchChitDetails();
    }
  }, [chit_uuid])

  const _fetchChitDetails = () => {
    fetchChitHistory(
      wm,
      {
        fields: ['net', 'chain_idx', 'chain_prev', 'chain_dgst', 'signature', 'clean', 'state', 'request', 'status', 'action', 
                'reference', 'memo', 'tally_uuid'],
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
  
  // Navigate to tally details
  const navigateToTally = () => {
    if (tallyDetails) {
      // For navigating we need the tallyDetails which has proper tally_ent field
      props.navigation.navigate('TallyPreview', {
        tally_seq: tallyDetails.tally_seq,
        tally_ent: tallyDetails.tally_ent,
        tally_uuid: tallyDetails.tally_uuid,
      });
    } else if (chit?.tally_uuid) {
      // If we don't have tallyDetails yet but have the UUID, navigate to a lookup route
      props.navigation.navigate('TallyPreview', {
        tally_uuid: chit.tally_uuid
      });
    }
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
        net: chit?.net, // Pass the raw units value instead of formatted string
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
          refreshing={loading || loadingTally}
          onRefresh={_fetchChitDetails}
        />
      }
    >
      {/* Partner Information Section */}
      {tallyDetails && (
        <View style={styles.section}>
          <Text style={styles.text}>
            <Text style={styles.labelText}>{talliesMeText?.part_cert?.title ?? 'Partner'}: </Text>
            {getPartnerName(tallyDetails)}
          </Text>
          <TouchableOpacity onPress={navigateToTally}>
            <Text style={styles.linkText}>
              <Text style={styles.labelText}>{talliesMeText?.tally_uuid?.title ?? 'Tally'}: </Text>
              {chit?.tally_uuid}
            </Text>
          </TouchableOpacity>
        </View>
      )}

      {/* Chit Details Section */}
      <View style={styles.section}>
        <Text style={styles.text}>
          <Text style={styles.labelText}>{chitsMeText?.chit_uuid?.title ?? ''}: </Text>
          {chit_uuid}
        </Text>
        <Text style={styles.text}>
          <Text style={styles.labelText}>{chitsMeText?.signature?.title ?? ''}: </Text>
          {chit?.signature}
        </Text>
        <View style={styles.rowContainer}>
          <Text style={[styles.labelText, styles.labelContainer]}>{chitsMeText?.net?.title ?? ''}: </Text>
          <ChipValue 
            units={chit?.net} 
            showIcon={true} 
            showCurrency={true}
            size="medium"
          />
        </View>
        <Text style={styles.text}>
          <Text style={styles.labelText}>{chitsMeText?.memo?.title ?? ''}: </Text>
          {chit?.memo}
        </Text>
      </View>

      {/* Status Section */}
      <View style={styles.section}>
        <Text style={styles.text}>
          <Text style={styles.labelText}>{chitsMeText?.clean?.title ?? ''}: </Text>
          {chit?.clean?.toString()}
        </Text>
        <Text style={styles.text}>
          <Text style={styles.labelText}>{chitsMeText?.request?.title ?? ''}: </Text>
          {chit?.request ?? 'None'}
        </Text>
        <Text style={styles.text}>
          <Text style={styles.labelText}>{chitsMeText?.status?.title ?? ''}: </Text>
          {chit?.status}
        </Text>
        <Text style={styles.text}>
          <Text style={styles.labelText}>{chitsMeText?.state?.title ?? ''}: </Text>
          {chit?.state}
        </Text>
        {/* Chain Information Section */}
        {chit?.chain_idx !== undefined && (
          <Text style={styles.text}>
            <Text style={styles.labelText}>{chitsMeText?.chain_idx?.title ?? 'Chain Index'}: </Text>
            {chit?.chain_idx}
          </Text>
        )}
        {chit?.chain_prev && (
          <Text style={styles.text}>
            <Text style={styles.labelText}>{chitsMeText?.chain_prev?.title ?? 'Previous Chain Hash'}: </Text>
            <Text style={styles.hashText}>
              {typeof chit.chain_prev === 'object' 
                ? JSON.stringify(chit.chain_prev) 
                : chit.chain_prev}
            </Text>
          </Text>
        )}
        {chit?.chain_dgst && (
          <Text style={styles.text}>
            <Text style={styles.labelText}>{chitsMeText?.chain_dgst?.title ?? 'Chain Digest'}: </Text>
            <Text style={styles.hashText}>
              {typeof chit.chain_dgst === 'object' 
                ? JSON.stringify(chit.chain_dgst) 
                : chit.chain_dgst}
            </Text>
          </Text>
        )}
      </View>

      {/* Technical Details Section (can be collapsed in future) */}
      <View style={styles.section}>
        <Text style={styles.text}>
          <Text style={styles.labelText}>{chitsMeText?.reference?.title ?? ''}: </Text>
          {JSON.stringify(chit?.reference ?? {})}
        </Text>
      </View>
    </ScrollView>
    {chit?.action ? <View style={styles.row}>
      <Button
        title={liftsPayMeText?.msg?.reject?.title ?? 'Refuse'}
        onPress={onRefuse}
        style={styles.refuse}
      />

      <Button
        title={charkText?.edit?.title ?? ''}
        onPress={onEdit}
        style={styles.edit}
      />

      <Button
        title={liftsPayMeText?.msg?.accept?.title ?? 'Pay'}
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
  section: {
    marginBottom: 20,
    borderBottomWidth: 1,
    borderBottomColor: colors.lightgray,
    paddingBottom: 10,
  },
  sectionTitle: {
    fontSize: 18,
    fontWeight: 'bold',
    color: colors.black,
    marginBottom: 10,
  },
  text: {
    fontSize: 15,
    color: colors.black,
    marginVertical: 5,
  },
  labelText: {
    fontWeight: '600',
    color: colors.gray300,
  },
  linkText: {
    fontSize: 15,
    color: colors.blue,
    marginVertical: 5,
    textDecorationLine: 'underline',
  },
  loadingContainer: {
    flex: 1,
    justifyContent: 'center',
    alignItems: 'center',
  },
  rowContainer: {
    flexDirection: 'row',
    alignItems: 'center',
    marginVertical: 5,
  },
  labelContainer: {
    marginRight: 8,
  },
  hashText: {
    fontSize: 13,
    fontFamily: 'monospace',
    color: colors.gray400,
    flexWrap: 'wrap',
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
