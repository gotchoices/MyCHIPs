import React, { useState } from 'react';
import {
  ScrollView,
  View,
  StyleSheet,
  RefreshControl,
  Keyboard,
} from 'react-native';

import { colors } from '../../../config/constants';
import useSocket from '../../../hooks/useSocket';
import useInvite from '../../../hooks/useInvite';
import { useTallyText } from '../../../hooks/useLanguage';
import useTallyUpdate from '../../../hooks/useTallyUpdate';

import CustomText from '../../../components/CustomText';
import Button from '../../../components/Button';
import Spinner from '../../../components/Spinner';
import TallyEditView from '../TallyEditView';

const EditTally = (props) => {
  const { tally_seq, tally_ent } = props.route?.params ?? {};
  const { wm } = useSocket();
  const { setTriggerInviteFetch } = useInvite();

  // Fetch tally text
  useTallyText(wm);

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
  } = useTallyUpdate(wm, tally_seq, tally_ent);

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

    wm.request('_tpt_ref', 'update', spec, (data, err) => {
      setUpdating(false);
      if(err) {
        return;
      }

      setTriggerInviteFetch(c => {
        return c + 1;
      })
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

        <View>
          <Button
            title={updating ? 'Updating...' : 'Update'}
            disabled={updating}
            onPress={onUpdate}
          />
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
})

export default EditTally;
