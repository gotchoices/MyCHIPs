import React, { useEffect, useState } from 'react';
import { ScrollView, View, Text, StyleSheet, TextInput } from 'react-native';
import { Picker } from '@react-native-picker/picker';

import { colors } from '../../../config/constants';
import useSocket from '../../../hooks/useSocket';

import CustomText from '../../../components/CustomText';
import CommonTallyView from '../CommonTallyView';
import Button from '../../../components/Button';

const EditOpenTally = (props) => {
  const { tally_seq, tally_ent } = props.route?.params ?? {};
  const { wm } = useSocket();

  const [loading, setLoading] = useState(true);
  const [tally, setTally] = useState();
  const [target, setTarget] = useState('');
  const [bound, setBound] = useState('');
  const [reward, setReward] = useState('');
  const [clutch, setClutch] = useState('');


  useEffect(() => {
    const spec = {
      fields: ['tally_uuid', 'tally_date', 'status', 'target', 'bound', 'reward', 'clutch'],
      view: 'mychips.tallies_v_me',
      where: {
        tally_ent,
        tally_seq,
      },
    }

    wm.request('_inv_ref', 'select', spec, data => {
      setLoading(false);
      if(data?.length) {
        const _tally = data?.[0];
        setTally(_tally);
        setTarget((_tally?.target ?? '').toString())
        setBound((_tally?.bound ?? '').toString())
        setReward((_tally?.reward ?? '').toString())
        setClutch((_tally?.clutch ?? '').toString())
      }
    });

  }, [])

  const onSave = () => {
    const data = {
      target: parseInt(target),
      bound: parseInt(bound),
      reward: parseFloat(reward),
      clutch: parseFloat(clutch),
    }

    console.log(data, 'data')
  }

  if(loading) {
    return (
      <View style={{ flex: 1, alignItems: 'center', justifyContent: 'center' }}>
        <Text>Loading...</Text>
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
    <ScrollView>
      <View style={styles.container}>
        <CommonTallyView tally={tally} />

        <View style={styles.detailControl}>
          <CustomText as="h4">
            Target
          </CustomText>

          <TextInput 
            value={target}
            style={[styles.input]}
            onChangeText={setTarget}
          />
        </View>

        <View style={styles.detailControl}>
          <CustomText as="h4">
            Bound
          </CustomText>

          <TextInput 
            value={bound}
            style={[styles.input]}
            onChangeText={setBound}
          />
        </View>

        <View style={styles.detailControl}>
          <CustomText as="h4">
            Reward 
          </CustomText>

          <TextInput 
            value={reward}
            style={[styles.input]}
            onChangeText={setReward}
          />
        </View>

        <View style={styles.detailControl}>
          <CustomText as="h4">
            Clutch
          </CustomText>

          <TextInput 
            value={clutch}
            style={[styles.input]}
            onChangeText={setClutch}
          />
        </View>

        <View>
          <Button
            title="Save" 
            onPress={onSave}
          />
        </View>
      </View>
    </ScrollView>
  )
}

const styles = StyleSheet.create({
  container: {
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

export default EditOpenTally;
