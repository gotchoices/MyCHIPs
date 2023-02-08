import React, { useEffect, useState } from 'react';
import { Picker } from '@react-native-picker/picker';
import {
  ScrollView,
  View,
  Text,
  StyleSheet,
  TextInput,
  RefreshControl,
  ActivityIndicator,
} from 'react-native';

import { colors } from '../../../config/constants';
import useSocket from '../../../hooks/useSocket';

import CustomText from '../../../components/CustomText';
import CommonTallyView from '../CommonTallyView';
import Button from '../../../components/Button';
import Spinner from '../../../components/Spinner';

const EditTally = (props) => {
  const { tally_seq, tally_ent } = props.route?.params ?? {};
  const { wm } = useSocket();

  const [updating, setUpdating] = useState(false);
  const [refreshing, setRefreshing] = useState(false);
  const [loading, setLoading] = useState(true);
  const [tally, setTally] = useState();
  const [tallyType, setTallyType] = useState('stock');
  const [contract, setContract] = useState('Tally_Contract');
  const [holdTerms, setHoldTerms] = useState({
    limit: 0,
    call: 0,
  });
  const [partTerms, setPartTerms] = useState({
    limit: 0,
    call: 0,
  });
  const [comment, setComment] = useState(comment);

  useEffect(() => {
    fetchTally();
  }, [])

  const fetchTally = (_refreshing = false) => {
    if(_refreshing) {
      setRefresing(true);
    }
    const spec = {
      fields: ['tally_uuid', 'tally_date', 'status', 'hold_terms', 'part_terms', 'part_cert', 'tally_type', 'comment', 'contract'],
      view: 'mychips.tallies_v_me',
      where: {
        tally_ent,
        tally_seq,
      }
    }

    wm.request('_inv_ref', 'select', spec, data => {
      setLoading(false);
      setRefreshing(false);
      const _tally = data?.[0];
      if(_tally) {
        setTally(data?.[0]);

        setTallyType(_tally.tally_type);
        setContract(_tally.contract?.terms ?? '');
        setComment(_tally.comment ?? '');
        setHoldTerms({
          limit: _tally.hold_terms?.limit,
          call: _tally.hold_terms?.call,
        })
        setPartTerms({
          limit: _tally.part_terms?.limit,
          call: _tally.part_terms?.call,
        })
      }
    });
  }

  const onHoldTermsChange = (name) => {
    return (value) => {
      setHoldTerms({
        ...holdTerms,
        [name]: 125,
      })
    }
  }

  const onPartTermsChange = (name) => {
    return (value) => {
      setPartTerms({
        ...partTerms,
        [name]: parseInt(value),
      })
    }
  }

  const onUpdate = () => {
    setUpdating(true);
    const data = {
      tally_type: tallyType,
      contract: {
        terms: contract,
      },
      hold_terms: holdTerms,
      part_terms: partTerms, 
      comment,
    }

    const spec = {
      fields: data,
      view: 'mychips.tallies_v_me',
      where: {
        tally_ent,
        tally_seq,
      },
    }

    wm.request('_tpt_ref', 'update', spec, data => {
      setUpdating(false);
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
      refreshControl={
        <RefreshControl
          refreshing={refreshing}
          onRefresh={fetchTally}
        />
      }
    >

      <View style={styles.container}>
        <CommonTallyView tally={tally} />

        <View style={styles.detailControl}>
          <CustomText as="h4">
            Tally Side
          </CustomText>

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
          <CustomText as="h4">
            Contract
          </CustomText>

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
          <CustomText as="h4">
            Credit terms
          </CustomText>

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
          <CustomText as="h4">
            Credit terms for partner
          </CustomText>

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
          <CustomText as="h4">
            Comment
          </CustomText>

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
  }
})

export default EditTally;
