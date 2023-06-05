import React, { useState } from 'react';
import {
  View,
  StyleSheet,
  ScrollView,
  Keyboard,
  RefreshControl,
} from 'react-native';
import Toast from 'react-native-toast-message';

import { colors } from '../../config/constants';
import { random } from '../../utils/common';
import useSocket from '../../hooks/useSocket';
import useCurrentUser from '../../hooks/useCurrentUser';
import { useTallyText } from '../../hooks/useLanguage';
import { offerTally, acceptTally, refuseTally } from '../../services/tally';
import useTallyUpdate from '../../hooks/useTallyUpdate';

import Button from '../../components/Button';
import CustomText from '../../components/CustomText';
import Spinner from '../../components/Spinner';
import TallyEditView from '../Tally/TallyEditView';

const TallyReview = (props) => {
  const { wm, tallyState } = useSocket();
  const { tally_seq } = props.route?.params ?? {};
  const { user } = useCurrentUser();
  const tally_ent = user?.curr_eid;

  // Fetch tally texts
  useTallyText(wm)

  const [updating, setUpdating] = useState(false);
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
  } = useTallyUpdate(wm, tally_seq, tally_ent, tallyState);

  const onOffer = () => {
    offerTally(wm, {
      tally_uuid: tally.tally_uuid,
      tally_ent,
      tally_seq,
    }).then(() => {
      Toast.show({
        type: 'success',
        text1: 'Tally signed.'
      })
    }).catch(err => {
      Toast.show({
        type: 'error',
        text1: err.message,
      });
    })
  }

  const onAccept = () => {
    acceptTally(wm, {
      tally_ent,
      tally_seq,
    }).then(() => {
      Toast.show({
        type: 'success',
        text1: 'Tally accepted',
      });
    }).catch(() => {
      return Toast.show({
        type: 'error',
        text1: err.message,
      });
    })
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
    }).catch(err => {
      Toast.show({
        type: 'error',
        text1: err.message,
      });
    })
  }

  const onUpdate = () => {
    Keyboard.dismiss();
    setUpdating(true);

    const payload = {
      tally_type: tallyType,
      contract: {
        terms: contract,
      },
      hold_terms: Object.keys(holdTerms).reduce((acc, key) => {
        acc[key] = holdTerms[key] ? parseInt(holdTerms[key]) : undefined;
        return acc;
      }, {}),
      part_terms: Object.keys(partTerms).reduce((acc, key) => {
        acc[key] = partTerms[key] ? parseInt(partTerms[key]) : undefined;
        return acc;
      }, {}),
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

    wm.request('update_tally' + random(), 'update', spec, (data, err) => {
      setUpdating(false);
      if(err) {
        Toast.show({
          type: 'error',
          text1: err.message,
        });
      }
    });
  }

  if(loading) {
    return (
      <View style={{ flex: 1, alignItems: 'center', justifyContent: 'center' }}>
        <Spinner text="Loading..." />
      </View>
    )
  }

  if(!tally) {
    return (
      <View style={{ flex: 1, alignItems: 'center' }}>
        <CustomText as="h2">
          Tally not found
        </CustomText>
      </View>
    )
  }

  return (
    <ScrollView
      keyboardShouldPersistTaps="handled"
      refreshControl={
        <RefreshControl
          refreshing={refreshing}
          onRefresh={fetchTally}
        />
      }
    >
      <View style={styles.container}>
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
          setContrac={setContract}
        />

        <View style={styles.actions}>
          {
            tally?.status === 'draft' && !!tally?.part_cert && (
              <Button
                style={{ marginRight: 10 }}
                title="Offer"
                onPress={onOffer}
              />
            )
          }

          {
            ['offer'].includes(tally?.status) && (
              <Button
                style={{ marginRight: 10 }}
                title="Accept"
                onPress={onAccept}
              />
            )
          }

          {
            ['draft', 'offer'].includes(tally?.status) && (
              <Button
                style={{ marginRight: 10 }}
                title={updating ? 'Updating...' : 'Update'}
                disabled={updating}
                onPress={onUpdate}
              />
            )
          }

          {
            ['draft', 'offer'] && (
              <Button
                title="Refuse"
                style={styles.refuseBtn}
                onPress={onRefuse}
              />
            )
          }
        </View>

      </View>
    </ScrollView>
  )
}

const styles = StyleSheet.create({
  container: {
    flex: 1,
    margin: 10,
    padding: 10,
    backgroundColor: colors.white,
  },
  actions: {
    flexDirection: 'row',
  },
  refuseBtn: {
    borderColor: colors.orangeRed,
    backgroundColor: colors.orangeRed,
  },
}) 

export default TallyReview;
