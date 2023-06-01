import React, { useEffect, useState, useRef } from 'react';
import { Picker } from '@react-native-picker/picker';
import {
  ScrollView,
  View,
  StyleSheet,
  TextInput,
  RefreshControl,
  Keyboard,
} from 'react-native';

import { colors } from '../../../config/constants';
import useSocket from '../../../hooks/useSocket';
import useInvite from '../../../hooks/useInvite';
import { useTallyText } from '../../../hooks/useLanguage';
import { fetchTallies } from '../../../services/tally';

import CustomText from '../../../components/CustomText';
import CommonTallyView from '../CommonTallyView';
import Button from '../../../components/Button';
import Spinner from '../../../components/Spinner';
import HelpText from '../../../components/HelpText';

const EditTally = (props) => {
  const { tally_seq, tally_ent } = props.route?.params ?? {};
  const { wm } = useSocket();
  const { setTriggerInviteFetch } = useInvite();
  const talliesText = useTallyText(wm);

  const [updating, setUpdating] = useState(false);
  const [refreshing, setRefreshing] = useState(false);
  const [loading, setLoading] = useState(true);
  const [tally, setTally] = useState();
  const [tallyType, setTallyType] = useState('stock');
  const [contract, setContract] = useState('Tally_Contract');
  const [holdTerms, setHoldTerms] = useState({
    limit: undefined,
    call: undefined,
  });
  const [partTerms, setPartTerms] = useState({
    limit: undefined,
    call: undefined,
  });
  const [comment, setComment] = useState(comment);

  useEffect(() => {
    _fetchTally();
  }, [wm])

  const _fetchTally = (_refreshing = false) => {
    if(_refreshing) {
      setRefreshing(true);
    }

    fetchTallies(wm, {
      fields: ['tally_uuid', 'tally_date', 'status', 'hold_terms', 'part_terms', 'part_cert', 'tally_type', 'comment', 'contract'],
      where: {
        tally_ent,
        tally_seq,
      }
    }).then((data) => {
      const _tally = data?.[0];
      if(_tally) {
        setTally(data?.[0]);
        const holdTermsLimit = _tally.hold_terms?.limit;

        setTallyType(_tally.tally_type);
        setContract(_tally.contract?.terms ?? '');
        setComment(_tally.comment ?? '');
        setHoldTerms({
          limit: holdTermsLimit?.toString(),
          call: _tally.hold_terms?.call?.toString(),
        })
        setPartTerms({
          limit: _tally.part_terms?.limit?.toString(),
          call: _tally.part_terms?.call?.toString(),
        })
      }
    }).finally(() => {
      setLoading(false);
      setRefreshing(false);
    })
  }

  const onHoldTermsChange = (name) => {
    return (value) => {
      setHoldTerms({
        ...holdTerms,
        [name]: value,
      })
    }
  }

  const onPartTermsChange = (name) => {
    return (value) => {
      setPartTerms({
        ...partTerms,
        [name]: value,
      })
    }
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
          onRefresh={_fetchTally}
        />
      }
    >

      <View style={styles.container}>
        <CommonTallyView tally={tally} />

        <View style={styles.detailControl}>
          <HelpText
            label={talliesText?.PCI?.title ?? ''}
            helpText={talliesText?.tally_type?.help}
            style={styles.headerText}
          />
          <Picker
            mode="dropdown"
            selectedValue={tallyType}
            style={styles.input}
            onValueChange={(item) => {
              setTallyType(item)
            }}
          >
            <Picker.Item label="Stock" value="stock" />
            <Picker.Item label="Foil" value="foil" />
          </Picker>
        </View>

        <View style={styles.detailControl}>

          <HelpText
            label={talliesText?.contract?.title ?? ''}
            helpText={talliesText?.contract?.help}
            style={styles.headerText}
          />
          <Picker
            mode="dropdown"
            style={styles.input}
            selectedValue={contract}
            onValueChange={(item) => {
              setContract(item)
            }}
          >
            <Picker.Item label="Tally Contract" value="Tally_Contract" />
          </Picker>
        </View>

        <View style={styles.detailControl}>
          <HelpText
            label={talliesText?.hold_terms?.title ?? ''}
            helpText={talliesText?.hold_terms?.help}
            style={styles.headerText}
          />

          <View style={{ marginVertical: 10 }}>
            <CustomText as="h5">
              Limit
            </CustomText>

            <TextInput 
              keyboardType='numeric'
              style={styles.input}
              value={holdTerms?.limit}
              onChangeText={onHoldTermsChange('limit')}
            />
          </View>

          <View>
            <CustomText as="h5">
              Call
            </CustomText>

            <TextInput 
              style={styles.input}
              keyboardType='numeric'
              value={holdTerms?.call}
              onChangeText={onHoldTermsChange('call')}
            />
          </View>
        </View>

        <View style={styles.detailControl}>
          <HelpText
            label={talliesText?.part_terms?.title ?? ''}
            helpText={talliesText?.part_terms?.help}
            style={styles.headerText}
          />

          <View style={{ marginVertical: 10 }}>
            <CustomText as="h5">
              Limit
            </CustomText>

            <TextInput 
              style={styles.input}
              keyboardType='numeric'
              value={partTerms?.limit}
              onChangeText={onPartTermsChange('limit')}
            />
          </View>

          <View>
            <CustomText as="h5">
              Call
            </CustomText>

            <TextInput
              style={styles.input}
              keyboardType='numeric'
              value={partTerms?.call}
              onChangeText={onPartTermsChange('call')}
            />
          </View>
        </View>

        <View style={styles.detailControl}>
          <HelpText
            label={talliesText?.comment?.title ?? ''}
            helpText={talliesText?.comment?.help}
            style={styles.headerText}
          />

          <TextInput 
            multiline
            numberOfLines={4}
            value={comment}
            style={[styles.input, styles.comment]}
            onChangeText={setComment}
          />
        </View>

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
