import React from 'react';
import { View, Text, StyleSheet, TouchableOpacity } from 'react-native';
import { useSelector } from 'react-redux';

import { colors } from '../../../config/constants';
import { ArrowBackwardIcon, ArrowForwardIcon, WarningIcon } from '../../../components/SvgAssets/SvgAssets';
import Avatar from '../../../components/Avatar/';
import { TallyTrainingIcon } from './TallyTrailingIcon';

const TemplateItem = (props) => {
  const item = props.template;
  const { imagesByDigest } = useSelector(state => state.avatar);

  const partCert = item.part_cert;
  const digest = partCert?.file?.[0]?.digest;
  const avatar = imagesByDigest[digest];

  const onView = () => {
    props.onItemSelected(item);
  }

  return (
    <TouchableOpacity style={[styles.row]} testID={props.testID} onPress={onView}>
      <View style={[styles.row, { height: 40, alignItems: 'center' }]}>
        {item?.tally_type === 'stock' ? <ArrowBackwardIcon /> : <ArrowForwardIcon />}
        <Avatar avatar={avatar} style={{ height: 40, width: 40, marginStart: 12 }} />
      </View>
      <View style={styles.itemContent}>
        {
          partCert ? <View style={styles.row}>
            <Text style={styles.name}>
              {partCert?.type === 'o'
                ? `${partCert?.name}`
                : `${partCert?.name?.first}${partCert?.name?.middle ? ' ' + partCert?.name?.middle + ' ' : ''} ${partCert?.name?.surname}`}
            </Text>

            <TallyTrainingIcon state={item?.state} hasPartCert={!!item?.part_cert} />
          </View> : <Text style={styles.name}>{props.draftLang}</Text>
        }
        <Text style={[styles.comment]} numberOfLines={1} ellipsizeMode='tail'>{item.comment}</Text>
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
    fontWeight: '400',
    fontFamily: 'inter'
  },
  comment: {
    fontSize: 14,
    color: '#636363',
    fontWeight: '500',
    fontFamily: 'inter',

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
