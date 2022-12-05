import React from 'react'; import { View, Image, Text, StyleSheet } from 'react-native';

import constants, { colors } from '../../../config/constants';
import { round } from '../../../utils/common';

import avatar from '../../../../assets/avatar.png';
import mychips from '../../../../assets/mychips.png';

const TallyItem = (props) => {
  const tally = props.tally;
  const net = round((tally?.net ?? 0) / 1000, 2);
  const dollar = round(net * constants.chipsToDollar, 2);
 
  return (
    <View style={styles.container}>
      {/*
        <Image 
          style={styles.avatar}
          source={avatar}
        />
      */}

      <View style={{ flex: 1,  }}>
        <Text style={styles.name}>{tally?.part_cert?.chad?.cid}</Text>
        <Text style={styles.description}>{tally?.part_cert?.chad?.agent}</Text>
      </View>

      <View style={styles.price}>
        <View style={styles.mychips}>
          <Image 
            source={mychips}
          />
          <Text style={net < 0 ? styles.mychipsNetNeg : styles.mychipsNet}>{net}</Text>
        </View>

        <Text style={dollar < 0 ? styles.dollarNeg : styles.dollar}>${dollar}</Text>
      </View>
    </View>
  )
}

const mychipsNet = {
  fontSize: 18,
  fontWeight: '600',
  color: colors.green,
};

const styles = StyleSheet.create({
  container: {
    flexDirection: 'row',
    justifyContent: 'space-between',
  },
  profile: {
    flexDirection: 'row',
  },
  avatar: {
    marginRight: 8,
    alignSelf: 'center',
  },
  name: {
    fontSize: 16,
    fontWeight: 'bold',
  },
  description: {
    fontSize: 11,
    color: colors.gray500,
  },
  price: {
    alignItems: 'flex-end',
  },
  mychips: {
    flexDirection: 'row',
    alignItems: 'center',
  },
  mychipsNet,
  mychipsNetNeg: {
    ...mychipsNet,
    color: colors.red,
  },
  dollar: {
    color: colors.green,
    fontSize: 10,
    fontWeight: '600',
  },
  dollarNeg: {
    color: colors.red,
    fontSize: 10,
    fontWeight: '600',
  },
})

export default TallyItem;

