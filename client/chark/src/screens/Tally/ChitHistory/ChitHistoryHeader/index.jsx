import React, { useEffect } from "react";
import { Image, StyleSheet, Text, View } from "react-native"
import { colors } from "../../../../config/constants";
import moment from 'moment';
import { round } from "../../../../utils/common";
import mychips from '../../../../../assets/mychips-large.png';
import mychipsNeg from '../../../../../assets/mychips-red-large.png';

const ChistHistoryHeader = (props, args) => {
  const { part_name, cid, date, net, runningBalance } = props.args ?? {};
  useEffect(() => {
    console.log("NET AMOUNT ==> ", net, runningBalance);
  }, [])
  const isNetNegative = net < 0;

  return <View>
    <View style={styles.container}>
      <View style={styles.row}>
        <View style={{ alignItems: 'flex-start' }}>
          <Text style={styles.label}>Running Balance</Text>
          <View style={[styles.row, { alignItems: 'center', justifyContent: 'center', marginTop: 4 }]}>
            <Image source={isNetNegative ? mychipsNeg : mychips} style={styles.image} resizeMode='contain' />
            <Text style={[styles.balance, { color: isNetNegative ? colors.red : colors.green }]}>{round((net ?? 0) / 1000, 3)}</Text>
          </View>
        </View>
        <Text style={styles.label}>{moment(date).format(`MMM DD, YYYY`)}</Text>
      </View>
      <View style={{ height: 20 }} />
      <Text style={styles.title}>{part_name}</Text>
      <Text style={[styles.sub, { marginTop: 4 }]}>Client ID: {cid}</Text>
    </View>
    <Text style={[
      styles.title,
      {
        color: '#14396C',
        fontWeight: 'bold',
        marginBottom: 12
      }
    ]}>
      Latest Chits
    </Text>
  </View>
}

const styles = StyleSheet.create({
  container: {
    borderRadius: 8,
    backgroundColor: colors.white,
    padding: 16,
    marginBottom: 12,
  },
  label: {
    color: colors.gray700,
    fontSize: 16,
  },
  balance: {
    fontSize: 26,
    fontWeight: '500',
  },
  title: {
    fontSize: 18,
    color: colors.gray700
  },
  sub: {
    fontSize: 14,
    color: colors.gray700
  },
  row: {
    flexDirection: 'row',
    justifyContent: 'space-between',
  },
  image: {
    height: 28,
    width: 26,
  }
})
export default ChistHistoryHeader;