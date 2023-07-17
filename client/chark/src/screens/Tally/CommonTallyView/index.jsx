import React, { useEffect } from 'react';
import { View, Text, StyleSheet, Image, Linking } from 'react-native';

import HelpText from '../../../components/HelpText';

import { colors, connectsMap } from '../../../config/constants';
import useMessageText from '../../../hooks/useMessageText';
import mychips from '../../../../assets/mychips-large.png';
import mychipsNeg from '../../../../assets/mychips-red-large.png';
import Button from '../../../components/Button';
import { round } from '../../../utils/common';
import { ChitIcon } from '../../../components/SvgAssets/SvgAssets';

const CommonTallyView = (props) => {
  const tally = props.tally;
  const { messageText } = useMessageText();

  const net = round((tally?.net ?? 0) / 1000, 3)
  const talliesText = messageText?.tallies;
  const hasPartCert = !!tally?.part_cert;
  const hasNet = !!tally?.net;
  const isNetNegative = tally?.net < 0;

  const connects = tally?.part_cert?.connect;
  const partCert = tally?.part_cert;

  const handleLinkPress = (link) => {
    Linking.canOpenURL(link)
      .then((supported) => {
        if (supported) {
          Linking.openURL(link);
        } else {
          console.log('Cannot open URL: ', link);
        }
      })
      .catch((error) => console.log('Error occurred:', error));
  };

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
              <ChitIcon color={isNetNegative ? colors.red : colors.green} height={14} width={14} />
              <Text style={isNetNegative ? styles.negativeText : styles.positiveText}>
                {net}
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

          {
            connects.length > 0 && <View>
              {
                connects.map((connect, index) => {
                  const link = connect.media === 'email' ? 'mailto:' : 'tel:';
                  return <View key={`${connect?.address}${index}`} style={styles.detailControl}>
                    <HelpText
                      label={connectsMap.get(connect.media) ?? connect.media}
                      style={styles.secondaryheader}
                    />
                    <Text onPress={() => { handleLinkPress(link + connect?.address) }}>{connect?.address}</Text>
                  </View>
                })
              }
            </View>
          }
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
