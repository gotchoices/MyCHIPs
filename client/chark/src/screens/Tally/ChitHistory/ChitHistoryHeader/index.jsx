import React, { useEffect, useMemo, useState } from "react";
import { Image, StyleSheet, Text, View } from "react-native"
import { colors } from "../../../../config/constants";
import { round } from "../../../../utils/common";
import useProfile from "../../../../hooks/useProfile";
import { getCurrency } from "../../../../services/user";
import { ChitIcon } from "../../../../components/SvgAssets/SvgAssets";
import { formatDate } from "../../../../utils/format-date";
import Avatar from "../../../../components/Avatar";

const ChistHistoryHeader = (props) => {
  const { part_name, cid, date, net, wm, avatar, totalBalance } = props.args ?? {};
  const { preferredCurrency } = useProfile();
  const [conversionRate, setConversionRate] = useState(undefined);
  const currencyCode = preferredCurrency.code;


  useEffect(() => {
    if (currencyCode) {
      getCurrency(wm, currencyCode).then(data => {
        setConversionRate(parseFloat(data?.rate ?? 0));
      }).catch(err => {
        // HANDLE ERROR CASE
      })
    }
  }, [currencyCode])

  const totalNetDollar = useMemo(() => {
    if (conversionRate) {
      const total = round((net ?? 0) / 1000, 3) * conversionRate;
      return round(total, 2);
    }

    return 0;
  }, [net, conversionRate])

  const isNetNegative = net < 0;

  return <View>
    <View style={styles.container}>
      <View style={styles.row}>
        <View style={{ alignItems: 'flex-start' }}>
          <Text style={[styles.label, { fontWeight: 'bold' }]}>Balance</Text>
          <View style={[styles.row, { alignItems: 'center', justifyContent: 'center', marginTop: 8 }]}>
            <ChitIcon color={isNetNegative ? colors.red : colors.green} height={28} width={24} />
            <Text style={[styles.balance, { color: isNetNegative ? colors.red : colors.green }]}>{round((net  ?? 0) / 1000, 3)}</Text>
          </View>
          {conversionRate && <Text style={styles.currency}>{currencyCode} {totalNetDollar}</Text>}
        </View>
        <Text style={styles.label}>{formatDate(date)}</Text>
      </View >
      <View style={[styles.row, { marginTop: 12 }]}>
        <Avatar
          style={styles.profileImage}
          avatar={avatar}
        />
        <View style={{ flex: 1, marginStart: 12, justifyContent: 'center' }}>
          <Text style={styles.title}>{part_name}</Text>
          <Text style={[styles.sub, { marginTop: 4 }]}>Client ID: {cid}</Text>
        </View>
      </View>
    </View >
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
  </View >
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
  currency: {
    fontSize: 14,
    color: colors.gray700,
    fontWeight: "bold",
    margin: 4,
  },
  profileImage: {
    width: 60,
    height: 60,
    borderRadius: 30,
  },
})
export default ChistHistoryHeader;