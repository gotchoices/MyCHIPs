import React, { useEffect, useState } from 'react';
import { ScrollView, View, Text, StyleSheet, TextInput } from 'react-native';

import { colors } from '../../../config/constants';
import useSocket from '../../../hooks/useSocket';
import { fetchTallies, fetchTradingVariables } from '../../../services/tally';
import { useTallyText } from '../../../hooks/useLanguage';

import CustomText from '../../../components/CustomText';
import CommonTallyView from '../CommonTallyView';
import Button from '../../../components/Button';

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
      fields: ['bound', 'reward', 'clutch', 'tally_seq', 'tally_uuid', 'tally_date', 'status', 'hold_terms', 'part_terms', 'part_cert', 'tally_type', 'comment', 'contract', 'net'],
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

  const showTradingVariables = () => {
    props.navigation.navigate('TradingVariables')
  }

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
      <View>
        <View style={styles.container}>
          <CommonTallyView
            tally={tally}
            onViewChitHistory={onViewChitHistory}
          />

          <View style={styles.detailControl}>
            <CustomText as="h4">
              Tally Type
            </CustomText>
            <Text style={styles.textInputStyle}>{tally.tally_type}</Text>
          </View>
        </View>

        <View style={styles.container}>
          <View style={styles.detailControl}>
            <CustomText as="h4">
              Holder Terms
            </CustomText>
            <Text style={styles.label}>Limit</Text>
            <Text style={styles.textInputStyle}>{tally.hold_terms.limit ?? 0}</Text>

            <Text style={styles.label}>Call</Text>
            <Text style={styles.textInputStyle}>{tally.hold_terms.call ?? 0}</Text>
          </View>
        </View>

        <View style={styles.container}>
          <View style={styles.detailControl}>
            <CustomText as="h4">
              Partner Terms
            </CustomText>
            <Text style={styles.label}>Limit</Text>
            <Text style={styles.textInputStyle}>{tally.part_terms.limit ?? 0}</Text>

            <Text style={styles.label}>Call</Text>
            <Text style={styles.textInputStyle}>{tally.part_terms.call ?? 0}</Text>
          </View>
        </View>

        <View style={styles.container}>
          <CustomText as="h4">
            Trading Variables
          </CustomText>

          <Button
            title="Show Trade"
            style={{ borderRadius: 12, width: 120, marginTop: 12 }}
            onPress={showTradingVariables}
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
  },
  textInputStyle: {
    paddingHorizontal: 10,
    paddingVertical: 16,
    color: 'black',
    fontSize: 16,
    backgroundColor: colors.gray100,
  },
  label: {
    marginTop: 8,
    fontSize: 14,
    color: 'black',
  }
})

export default EditOpenTally;
