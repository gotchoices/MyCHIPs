import React, { useEffect, useMemo, useState } from 'react';
import {
  ScrollView,
  View,
  StyleSheet,
  RefreshControl,
  Keyboard,
  Alert,
  Platform,
  KeyboardAvoidingView,
} from 'react-native';

import { colors, keyServices } from '../../../config/constants';
import useSocket from '../../../hooks/useSocket';
import useInvite from '../../../hooks/useInvite';
import { useHoldTermsText, useTallyText } from '../../../hooks/useLanguage';
import useTallyUpdate from '../../../hooks/useTallyUpdate';
import { fetchContracts, updateHoldCert } from '../../../services/tally';

import CustomText from '../../../components/CustomText';
import Button from '../../../components/Button';
import Spinner from '../../../components/Spinner';
import TallyEditView from '../TallyEditView';
import { Toast } from 'react-native-toast-message/lib/src/Toast';
import { offerTally, acceptTally, refuseTally } from '../../../services/tally';
import { createSignature, verifySignature } from '../../../utils/message-signature';
import { retrieveKey } from '../../../utils/keychain-store';
import { GenerateKeysDialog } from './GenerateKeysDialog';
import { UpdateHoldCert } from './UpdateHoldCert';
import CenteredModal from '../../../components/CenteredModal';

const TallyPreview = (props) => {
  const { tally_seq, tally_ent } = props.route?.params ?? {};
  const { wm } = useSocket();
  const { setTriggerInviteFetch } = useInvite();

  const [showDialog, setShowDialog] = useState(false);
  const [updating, setUpdating] = useState(false);
  const [sig, setSig] = useState(undefined);
  const [json, setJson] = useState(undefined);
  const [tallyContracts, setTallyContracts] = useState([]);
  const [updateCert, setUpdateCert] = useState(false);

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
    fetchContracts(wm, {
      fields: ['top', 'name', 'title', 'language', 'host', 'rid', 'clean'],
      where: { top: true },
    }).then((data) => {
      setTallyContracts(data);
    })
  }, [])


  const onDisplayCertUpdate = () => {
    setUpdateCert(true);
  }

  const onDismissCertUpdate = () => {
    setUpdateCert(false);
  }

  useEffect(() => {
    setJson(tally?.json);
  }, [tally])

  // Fetch tally text
  useTallyText(wm);
  useHoldTermsText(wm);

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

  // Update returns success but still not updating hold_cert
  const onUpdateCert = (cert) => {
    onDismissCertUpdate();
    console.log("NEW_UPDATE_VALUE ==> ", typeof cert);
    updateHoldCert(wm, {
      hold_cert: cert,
      tally_ent,
      tally_seq,
    }).then(result => {
      fetchTally();

      Toast.show({
        type: 'success',
        text1: 'Certificate updated successfully.',
      });
    }).catch(ex => {
      console.log("EXCEPTION_HERE ==> ", ex);
    });
  }

  const onUpdate = () => {
    Keyboard.dismiss();

    setUpdating(true);

    const payload = {
      tally_type: tallyType,
      hold_terms: holdTermsData,
      part_terms: partTermsData,
      comment,
    }

    if (contract) {
      const found = tallyContracts?.find((item) => item.rid === contract)
      if (found) {
        payload.contract = {
          rid: found.rid,
        };
      }
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

  const onAccept = async () => {
    if (!json) {
      Alert.alert("Tally can not be signed");
      return;
    }
    createSignature(JSON.stringify(json)).then(signature => {
      setSig(signature);
      return acceptTally(
        wm, { tally_ent, tally_seq, signature },
      );
    }).then((result) => {
      Toast.show({
        type: 'success',
        text1: 'Tally accepted',
      });
      props.navigation.goBack();
    }).catch(err => {
      const { isKeyAvailable, message } = err;
      if (isKeyAvailable === false) {
        Alert.alert(
          "Create Keys",
          "Seems like there is no key to create signature please continue to create one and accept tally.",
          [
            { text: "Cancel" },
            { text: "Continue", onPress: showGenerateKey }
          ]
        );
      } else {
        Alert.alert("Error", message || err);
      }
    });
  }
  const showGenerateKey = () => {
    setShowDialog(true);
  }

  const dismissGenerateKey = () => {
    setShowDialog(false);
  }

  const onViewContract = () => {
    props.navigation.navigate("TallyContract", { tally_seq });
  }

  const onRefuse = () => {
    refuseTally(wm, {
      tally_ent,
      tally_seq,
    }).then(() => {
      Toast.show({
        type: 'success',
        text1: 'Tally refused.'
      });
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
    <>
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
            onViewContract={onViewContract}
            tallyContracts={tallyContracts}
            onUpdateContract={() => {
              onDisplayCertUpdate();
            }}
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
            testID="offerBtn"
          />

          <CustomButton
            show={canAccept}
            title="Accept"
            onPress={onAccept}
            style={{ marginLeft: 10 }}
            testID="acceptBtn"
          />

          <CustomButton
            show={canRefuse}
            title="Refuse"
            onPress={onRefuse}
            style={styles.refuse}
          />
        </View>
      </KeyboardAvoidingView>
      <GenerateKeysDialog
        visible={showDialog}
        onDismiss={dismissGenerateKey}
        onError={(err) => {
          Alert.alert("Error", err);
        }}
        onKeySaved={() => {
          Alert.alert("Success", "Key is generated successfully now you can accept tally.");
        }}
      />
      <CenteredModal
        isVisible={updateCert}
        onClose={onDismissCertUpdate}
      >
        <UpdateHoldCert
          onUpdateCert={onUpdateCert}
          onDismiss={onDismissCertUpdate}
          tallyCurrentHoldCert={tally?.hold_cert}
        />
      </CenteredModal>
    </>
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
      testID={props?.testID}
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
