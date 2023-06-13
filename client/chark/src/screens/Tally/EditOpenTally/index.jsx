import React, { useEffect, useState } from 'react';
import { ScrollView, View, Text, StyleSheet, TextInput } from 'react-native';

import { colors } from '../../../config/constants';
import useSocket from '../../../hooks/useSocket';
import { fetchTallies } from '../../../services/tally';
import { useTallyText } from '../../../hooks/useLanguage';

import CustomText from '../../../components/CustomText';
import CommonTallyView from '../CommonTallyView';
import Button from '../../../components/Button';
import HelpText from '../../../components/HelpText';
import { err } from 'react-native-svg/lib/typescript/xml';

const EditOpenTally = (props) => {
  const { tally_seq, tally_ent } = props.route?.params ?? {};
  const { wm } = useSocket();
  useTallyText(wm);

  const [loading, setLoading] = useState(true);
  const [tally, setTally] = useState();
  const [target, setTarget] = useState('');
  const [bound, setBound] = useState('');
  const [reward, setReward] = useState('');
  const [clutch, setClutch] = useState('');


  // fields: ['tally_uuid', 'tally_date', 'status', 'target', 'bound', 'reward', 'clutch', 'part_cert'],
  useEffect(() => {
    fetchTallies(wm, {
      fields: ['credit', 'bound', 'reward', 'clutch', 'tally_seq', 'tally_uuid', 'tally_date', 'status', 'hold_terms', 'part_terms', 'part_cert', 'tally_type', 'comment', 'contract', 'net'],
      where: {
        tally_ent,
        tally_seq,
      },
    }).then(data => {
      if (data?.length) {
        const _tally = data?.[0];
        setTally(_tally);
        setTarget((_tally?.target ?? '').toString())
        setBound((_tally?.bound ?? '').toString())
        setReward((_tally?.reward ?? '').toString())
        setClutch((_tally?.clutch ?? '').toString())
      }
    }).catch((e) => {
      console.log("ERROR===>", e);
    }).finally(() => {
      setLoading(false);
    })
  }, [tally_seq, tally_ent])

  const onSave = () => {
    const data = {
      target: parseInt(target),
      bound: parseInt(bound),
      reward: parseFloat(reward),
      clutch: parseFloat(clutch),
    }

    console.log(data, 'data')
  }

  if (loading) {
    return (
      <View style={{ flex: 1, alignItems: 'center', justifyContent: 'center' }}>
        <Text>Loading...</Text>
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
  const onViewChitHistory = () => {
    props.navigation.navigate('ChitHistory', {
      tally_seq,
      tally_ent,
    });
  }

  return (
    <ScrollView>
      <View style={styles.container}>

        <CommonTallyView
          tally={tally}
          onViewChitHistory={onViewChitHistory}
        />

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
