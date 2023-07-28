import React, { useEffect, useState } from 'react';
import { ScrollView, View, Text, StyleSheet, TextInput } from 'react-native';

import { colors } from '../../../config/constants';
import useSocket from '../../../hooks/useSocket';
import { fetchTallies, fetchTradingVariables } from '../../../services/tally';
import { useHoldTermsText, useTallyText } from '../../../hooks/useLanguage';

import CustomText from '../../../components/CustomText';
import CommonTallyView from '../CommonTallyView';
import Button from '../../../components/Button';
import HelpText from '../../../components/HelpText';
import useMessageText from '../../../hooks/useMessageText';

const EditOpenTally = (props) => {
  const { tally_seq, tally_ent } = props.route?.params ?? {};
  const { wm } = useSocket();
  const tallyText = useTallyText(wm);

  const [loading, setLoading] = useState(true);
  const [tally, setTally] = useState();
  const [target, setTarget] = useState('');
  const [bound, setBound] = useState('');
  const [reward, setReward] = useState('');
  const [clutch, setClutch] = useState('');
  useHoldTermsText(wm);
  const { messageText } = useMessageText();
  const holdTermsText = messageText?.terms_lang?.hold_terms?.values;
  const partTermsText = messageText?.terms_lang?.part_terms?.values;


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

    const partCert = tally?.part_cert;
    console.log("DIGEST_HAVE ==> ", JSON.stringify(partCert));
    props.navigation.navigate('ChitHistory', {
      tally_seq: tally?.tally_seq,
      tally_ent,
      tally_uuid: tally?.tally_uuid,
      part_name: `${partCert?.name?.first}${partCert?.name?.middle ? ' ' + partCert?.name?.middle + ' ' : ''} ${partCert?.name?.surname}`,
      digest: partCert?.file?.[0]?.digest,
      date: tally?.tally_date,
      net: tally?.net,
      cid: partCert?.chad?.cid,
    });
  }

  const onPay = () => {
    props.navigation.navigate(
      "PaymentDetail",
      {
        tally_uuid: tally?.tally_uuid,
        chit_seq: tally?.tally_seq,
      }
    );
  }

  return (
    <ScrollView>
      <View>
        <View style={styles.container}>
          <CommonTallyView
            tally={tally}
            onViewChitHistory={onViewChitHistory}
            onPay={onPay}
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
            <HelpText
              label={tallyText?.hold_terms?.title ?? ''}
              helpText={tallyText?.hold_terms?.help}
              style={styles.label}
            />
            {
              holdTermsText?.map((holdTerm, index) => {
                return <View key={`${holdTerm?.value}${index}`} style={{ marginVertical: 10 }}>
                  <HelpText
                    label={holdTerm?.title ?? ''}
                    helpText={holdTerm?.help}
                    style={styles.h5}
                  />

                  <Text style={styles.textInputStyle}>{tally.hold_terms?.[holdTerm?.value] ?? 0}</Text>
                </View>
              })
            }
          </View>
        </View>

        <View style={styles.container}>
          <View style={styles.detailControl}>
            <HelpText
              label={tallyText?.part_terms?.title ?? ''}
              helpText={tallyText?.part_terms?.help}
              style={styles.headerText}
            />
            {
              partTermsText?.map((partTerm, index) => {
                return <View key={`${partTerm?.value}${index}`} style={{ marginVertical: 10 }}>
                  <HelpText
                    label={partTerm?.title ?? ''}
                    helpText={partTerm?.help}
                    style={styles.h5}
                  />

                  <Text style={styles.textInputStyle}>{tally.part_terms?.[partTerm?.value] ?? 0}</Text>
                </View>
              })
            }
          </View>
        </View>

        <View style={styles.container}>
          <HelpText
            label={'Trading Variables'}
            style={styles.headerText}
          />

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
  },
  headerText: {
    fontSize: 14,
    color: 'black',
  }
})

export default EditOpenTally;
