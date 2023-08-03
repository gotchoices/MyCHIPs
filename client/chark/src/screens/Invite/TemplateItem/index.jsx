import React from 'react';
import { View, Text, StyleSheet, TouchableOpacity } from 'react-native';
import useMessageText from '../../../hooks/useMessageText';
import { colors } from '../../../config/constants';
import { ArrowBackwardIcon, ArrowForwardIcon, WarningIcon } from '../../../components/SvgAssets/SvgAssets';
import Avatar from '../../../components/Avatar/';
import { TallyTrainingIcon } from './TallyTrailingIcon';

const TemplateItem = (props) => {
  const item = props.template;
  const { messageText } = useMessageText();
  const tallyText = messageText?.tallies ?? {};
  const partCert = item.part_cert;

  const onView = () => {
    props.navigation.navigate('TallyPreview', {
      tally_seq: item.id,
      tally_ent: item.tally_ent,
    });
  }

  return (
    <TouchableOpacity style={[styles.row]} testID={props.testID} onPress={onView}>
      <View style={[styles.row, { height: 40, alignItems: 'center' }]}>
        {item?.tally_type === 'stock' ? <ArrowBackwardIcon /> : <ArrowForwardIcon />}
        <Avatar style={{ height: 40, width: 40, marginStart: 12 }} />
      </View>
      <View style={styles.itemContent}>
        {
          partCert ? <View style={styles.row}>
            <Text style={styles.name}>
              {`${partCert?.name?.first}${partCert?.name?.middle ? ' ' + partCert?.name?.middle + ' ' : ''} ${partCert?.name?.surname}`}
            </Text>
            <TallyTrainingIcon status={item.status} />
          </View> : <Text style={styles.name}>Beginning template</Text>
        }
        <Text style={[styles.comment]}>{item.comment}</Text>
      </View>
    </TouchableOpacity>
  );
}

const itemStyle = {
  borderWidth: 1,
  borderColor: '#DDD',
  borderRadius: 5,
  padding: 10,
  marginBottom: 1,
}

const styles = StyleSheet.create({
  container: {
    marginBottom: 5,
  },
  item: itemStyle,
  row: {
    flexDirection: 'row',
  },
  name: {
    fontSize: 16,
    color: colors.black,
    fontWeight: '400'
  },
  comment: {
    fontSize: 14,
    color: '#636363',
    fontWeight: '500',
  },
  itemContent: {
    borderBottomWidth: 1,
    borderColor: '#BBBBBB',
    flex: 1,
    marginStart: 16,
    paddingBottom: 16,
  }
})

export default TemplateItem;
