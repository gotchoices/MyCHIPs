import React, { useEffect, useMemo, useState } from 'react';
import {
  ScrollView,
  View,
  StyleSheet,
  RefreshControl,
  Keyboard,
  Alert,
  KeyboardAvoidingView,
} from 'react-native';

import { colors, keyServices } from '../../../config/constants';
import useSocket from '../../../hooks/useSocket';
import useInvite from '../../../hooks/useInvite';
import { useTallyText } from '../../../hooks/useLanguage';
import useTallyUpdate from '../../../hooks/useTallyUpdate';

import CustomText from '../../../components/CustomText';
import Button from '../../../components/Button';
import Spinner from '../../../components/Spinner';
import TallyEditView from '../TallyEditView';
import { Toast } from 'react-native-toast-message/lib/src/Toast';
import { offerTally, acceptTally, refuseTally } from '../../../services/tally';
import { createSignature, verifySignature } from '../../../utils/message-signature';
import { retrieveKey } from '../../../utils/keychain-store';

const TallyPreview = (props) => {
  const { tally_seq, tally_ent } = props.route?.params ?? {};
  const { wm } = useSocket();
  const { setTriggerInviteFetch } = useInvite();

  const [updating, setUpdating] = useState(false);
  const [sig, setSig] = useState(undefined);
  const [json, setJson] = useState(undefined);

  const {
    loading,
    refreshing,
    tally,
    tallyType,
    contract,
    holdTerms,
    partTerms,
    comment,
    setComment,
    onHoldTermsChange,
    onPartTermsChange,
    setTallyType,
    setContract,
    fetchTally,
    setTally
  } = useTallyUpdate(wm, tally_seq, tally_ent);

  useEffect(() => {
    setJson(tally?.json);
  }, [tally])

  // Fetch tally text
  useTallyText(wm);

  const onShare = () => {
    const hold_limit = tally?.hold_terms?.limit;
    const part_limit = tally?.part_terms?.limit;
    if (
      typeof hold_limit === 'undefined' || hold_limit === null ||
      typeof part_limit === 'undefined' || part_limit === null
    ) {
      return Toast.show({
        type: 'error',
        text1: 'Please add hold terms and part terms before sharing tally.',
      });
    }

    return props.navigation.navigate(
      "TallyShare",
      {
        tally_id: tally.tally_seq,
      }
    );
  }

  const holdTermsData = Object.keys(holdTerms).reduce((acc, key) => {
    acc[key] = holdTerms[key] ? parseInt(holdTerms[key]) : undefined;
    return acc;
  }, {});

  const partTermsData = Object.keys(partTerms).reduce((acc, key) => {
    acc[key] = partTerms[key] ? parseInt(partTerms[key]) : undefined;
    return acc;
  }, {});

  const onUpdate = () => {
    Keyboard.dismiss();
    setUpdating(true);

    const payload = {
      tally_type: tallyType,
      contract: {
        terms: contract,
      },
      hold_terms: holdTermsData,
      part_terms: partTermsData,
      comment,
    }

    const spec = {
      fields: payload,
      view: 'mychips.tallies_v_me',
      where: {
        tally_ent,
        tally_seq,
      },
    }

    wm.request('_tpt_ref', 'update', spec, (data, err) => {
      setUpdating(false);
      if (err) {
        return Toast.show({
          type: 'error',
          text1: err?.message ?? 'Error updating tally',
        });
      }

      setTally({
        ...tally,
        hold_terms: {
          ...(tally?.hold_terms ?? {}),
          ...holdTermsData
        },
        part_terms: {
          ...(tally?.part_terms ?? {}),
          ...partTermsData,
        },
      });

      setTriggerInviteFetch(c => {
        return c + 1;
      });
    });
  }

  const onOffer = () => {
    offerTally(wm, {
      tally_uuid: tally.tally_uuid,
      tally_ent,
      tally_seq,
    }).then(() => {
      Toast.show({
        type: 'success',
        text1: 'Offer is processed.',
      });
      props.navigation.goBack();
    }).catch(err => {
      Toast.show({
        type: 'error',
        text1: err.message,
      });
    })
  }

  const onAccept = () => {
    if (!json) {
      Alert.alert("Tally can't be signed");
      return;
    }
    createSignature(JSON.stringify(json)).then(signature => {
      setSig(signature);
      console.log("Signature ==> ", signature);
      return acceptTally(
        wm, { tally_ent, tally_seq, signature },
      );
    }).then((result) => {
      console.log("RESULT ==> ", result);
      Toast.show({
        type: 'success',
        text1: 'Tally accepted',
      });
      props.navigation.goBack();
    }).catch(ex => {
      console.log("Exception ==> ", ex);
    });

    /* acceptTally(wm, {
      tally_ent,
      tally_seq,
    }).then(() => {
      Toast.show({
        type: 'success',
        text1: 'Tally accepted',
      });
      props.navigation.goBack();
    }).catch(() => {
      return Toast.show({
        type: 'error',
        text1: err.message,
      });
    }) */
  }

  const onRefuse = () => {
    refuseTally(wm, {
      tally_ent,
      tally_seq,
    }).then(() => {
      Toast.show({
        type: 'success',
        text1: 'Tally refused.'
      })
      props.navigation.goBack();
    }).catch(err => {
      Toast.show({
        type: 'error',
        text1: err.message,
      });
    })
  }

  const onVerify = async () => {
    const creds = await retrieveKey(keyServices.publicKey);
    verifySignature(sig, JSON.stringify(json), creds.password)
      .then((verified) => {
        if (verified) {
          console.log("Verified Successfully");
        } else {
          console.log("Verified Failed");
        }
      })
      .catch(ex => console.log("Exception ==> ", ex))
  }

  if (loading) {
    return (
      <View style={{ flex: 1, alignItems: 'center', justifyContent: 'center' }}>
        <Spinner text="Loading..." />
      </View>
    )
  }

  if (!tally) {
    return (
      <View style={{ flex: 1, alignItems: 'center' }}>
        <CustomText as="h2">
          Tally not found
        </CustomText>
      </View>
    )
  }

  const hasPartCert = !!tally?.part_cert;
  const canUpdate = !hasPartCert || ['offer', 'draft'].includes(tally.status);
  const canShare = !hasPartCert && tally.status === 'draft';
  const canOffer = hasPartCert && tally.status === 'draft';
  const canAccept = hasPartCert && tally.status === 'offer';
  const canRefuse = hasPartCert && tally.status === 'offer';

  return (
    <KeyboardAvoidingView
      style={[styles.container]}
      behavior={Platform.OS === 'ios' ? "padding" : undefined}
      keyboardVerticalOffset={Platform.OS === 'ios' ? 100 : 0}
    >

      <ScrollView
        style={styles.container}
        contentContainerStyle={styles.contentContainer}
        keyboardShouldPersistTaps="handled"
        refreshControl={
          <RefreshControl
            refreshing={refreshing}
            onRefresh={fetchTally}
          />
        }
      >
        <TallyEditView
          tally={tally}
          tallyType={tallyType}
          contract={contract}
          holdTerms={holdTerms}
          partTerms={partTerms}
          comment={comment}
          setComment={setComment}
          onHoldTermsChange={onHoldTermsChange}
          onPartTermsChange={onPartTermsChange}
          setTallyType={setTallyType}
          setContract={setContract}
        />
      </ScrollView>

      <View style={styles.actions}>
        <CustomButton
          show={canUpdate}
          title={updating ? 'Updating...' : 'Update'}
          disabled={updating}
          onPress={onUpdate}
        />

        <CustomButton
          show={canShare}
          title="Share"
          onPress={onShare}
          style={styles.shareButton}
        />

        <CustomButton
          show={canOffer}
          title="Offer"
          onPress={onOffer}
          style={styles.shareButton}
        />

        <CustomButton
          show={canAccept}
          title="Accept"
          onPress={onAccept}
          style={{ marginLeft: 10 }}
        />

        <CustomButton
          show={canRefuse}
          title="Refuse"
          onPress={onRefuse}
          style={styles.refuse}
        />
      </View>
    </KeyboardAvoidingView>
  )
}

function CustomButton(props) {
  if (!props.show) return null;

  return (
    <Button
      title={props.title}
      disabled={props.disabled ?? false}
      onPress={props.onPress}
      style={props.style ?? {}}
    />
  )
}

const styles = StyleSheet.create({
  container: {
    flex: 1,
  },
  contentContainer: {
    backgroundColor: 'white',
    margin: 10,
    padding: 10,
  },
  toolbar: {
    flexDirection: 'row',
    padding: 16,
    height: 56,
    alignItems: 'center',
    backgroundColor: 'white',
    elevation: 8,
  },
  detailControl: {
    marginVertical: 10
  },
  input: {
    paddingHorizontal: 10,
    paddingVertical: 10,
    backgroundColor: colors.gray100,
  },
  comment: {
    textAlignVertical: 'top',
  },
  headerText: {
    color: colors.black,
    fontSize: 14,
  },
  shareButton: {
    marginLeft: 10,
    borderColor: colors.quicksilver,
    backgroundColor: colors.quicksilver,
  },
  refuse: {
    backgroundColor: colors.orangeRed,
    borderColor: colors.orangeRed,
    marginLeft: 10,
  },
  actions: {
    margin: 10,
    flexDirection: 'row',
    backgroundColor: 'white',
    padding: 10,
  }
})

export default TallyPreview;
