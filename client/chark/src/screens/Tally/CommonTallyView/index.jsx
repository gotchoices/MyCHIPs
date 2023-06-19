import React from 'react';
import { View, Text, StyleSheet, Image } from 'react-native';

import HelpText from '../../../components/HelpText';

import { colors } from '../../../config/constants';
import useMessageText from '../../../hooks/useMessageText';
import mychips from '../../../../assets/mychips-large.png';
import mychipsNeg from '../../../../assets/mychips-red-large.png';
import Button from '../../../components/Button';

const CommonTallyView = (props) => {
  const tally = props.tally;
  const { messageText } = useMessageText();

  const talliesText = messageText?.tallies;
  const hasPartCert = !!tally?.part_cert;
  const hasNet = !!tally?.net;
  const isNetNegative = tally?.net < 0;

  const partCert = tally?.part_cert;


  return (
    <View>
      {
        hasNet && <View style={styles.detailControl}>
          <HelpText
            label={talliesText?.net?.title ?? 'Tally balance'}
            helpText={talliesText?.net?.help}
            style={styles.headerText}
          />
          <View>
            <View style={styles.row}>
              <Image source={isNetNegative ? mychipsNeg : mychips} style={styles.image} resizeMode='contain' />
              <Text style={isNetNegative ? styles.negativeText : styles.positiveText}>
                {tally.net}
              </Text>
            </View>
            <Button
              title='Chit History'
              onPress={props.onViewChitHistory}
              style={{ borderRadius: 12, width: 120, marginTop: 12 }}
            />
          </View>
        </View>
      }
      {
        hasPartCert && <View style={styles.detailControl}>
          <HelpText
            label={'Partner Details'}
            style={styles.headerText}
          />

          <View style={styles.detailControl}>
            <HelpText
              label={'Full Name'}
              style={styles.secondaryheader}
            />
            <Text>{`${partCert?.name?.first}${partCert?.name?.middle ? ' ' + partCert?.name?.middle + ' ' : ''} ${partCert?.name?.surname}`}</Text>
          </View>

          <View style={styles.detailControl}>
            <HelpText
              label={'CID'}
              style={styles.secondaryheader}
            />
            <Text>{partCert?.chad?.cid}</Text>
          </View>

          <View style={styles.detailControl}>
            <HelpText
              label={'Agent ID'}
              style={styles.secondaryheader}
            />
            <Text>{partCert?.chad?.agent}</Text>
          </View>
        </View>
      }

      <View style={styles.detailControl}>
        <HelpText
          label={talliesText?.tally_uuid?.title ?? ''}
          helpText={talliesText?.tally_uuid?.help}
          style={styles.headerText}
        />
        <Text>
          {tally.tally_uuid}
        </Text>
      </View>

      <View style={styles.detailControl}>
        <HelpText
          label={talliesText?.tally_date?.title ?? ''}
          helpText={talliesText?.tally_date?.help}
          style={styles.headerText}
        />
        <Text>
          {new Date(tally.tally_date).toLocaleString()}
        </Text>
      </View>

      <View style={styles.detailControl}>
        <HelpText
          label={talliesText?.status?.title ?? ''}
          helpText={talliesText?.status?.help}
          style={styles.headerText}
        />

        <Text>
          {tally.status}
        </Text>
      </View>
    </View>
  )
}

const styles = StyleSheet.create({
  detailControl: {
    marginVertical: 10
  },
  headerText: {
    color: colors.black,
    fontSize: 14,
  },
  secondaryheader: {
    color: colors.black,
    fontSize: 13,
    fontWeight: 'normal',
  },
  label: {
    fontWeight: 'bold',
    color: colors.black,
    fontSize: 14
  },
  image: {
    height: 14,
    width: 14
  },
  positiveText: {
    color: 'green'
  },
  negativeText: {
    color: 'red',
  },
  row: {
    flexDirection: 'row',
    alignItems: 'center',
  }
})

export default CommonTallyView;
