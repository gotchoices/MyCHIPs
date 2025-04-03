import React, { useEffect, useMemo, useState } from "react";
import { StyleSheet, Text, View } from "react-native"
import { useSelector } from 'react-redux';

import { colors } from "../../../../config/constants";
import { round, unitsToChips, unitsToFormattedChips } from "../../../../utils/common";
import { getCurrency } from "../../../../services/user";
import Avatar from "../../../../components/Avatar";
import ChipValue from "../../../../components/ChipValue";
import useMessageText from "../../../../hooks/useMessageText";

const ChistHistoryHeader = (props) => {
  const { part_name, cuid, net, wm, avatar, net_pc } = props.args ?? {};
  const { preferredCurrency } = useSelector(state => state.profile);
  const [conversionRate, setConversionRate] = useState(undefined);
  const currencyCode = preferredCurrency.code;

  const { messageText } = useMessageText();
  const chitMeText = messageText?.chits_v_me?.col;

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
      const chips = unitsToChips(net ?? 0);
      const total = chips * conversionRate;
      return round(total, 2);
    }

    return 0;
  }, [net, conversionRate])

  const pendingText = useMemo(() => {
    return chitMeText?.status?.values?.find(s => s.value === 'pend');
  }, [chitMeText?.status?.values])

  // Calculate pending amount (difference between pending and current)
  const pendingAmount = useMemo(() => {
    if (net_pc !== undefined && net !== undefined) {
      const pendingValue = Number(net_pc);
      const currentValue = Number(net);
      const difference = pendingValue - currentValue;
      
      // Only return a value if there's a non-zero difference
      if (difference !== 0) {
        return unitsToFormattedChips(difference);
      }
    }
    return null;
  }, [net_pc, net]);

  return (
    <View style={styles.container}>
      <View style={styles.layout}>
        {/* Left side - User info with avatar */}
        <View style={styles.userInfoContainer}>
          <Avatar
            style={styles.profileImage}
            avatar={avatar}
          />
          <View style={styles.userTextContainer}>
            <Text style={styles.userName}>{part_name}</Text>
            <Text style={styles.userId}>Client ID: {cuid}</Text>
          </View>
        </View>

        {/* Right side - CHIP values */}
        <View style={styles.valueContainer}>
          {/* Show pending amount only if there's a non-zero difference */}
          {pendingAmount && (
            <Text style={styles.pendingText}>
              {pendingText?.title ?? 'Pending'}: {pendingAmount}
            </Text>
          )}
          
          {/* Tally total */}
          <ChipValue 
            value={unitsToFormattedChips(net ?? 0)}
            currencyValue={totalNetDollar}
            currencyCode={currencyCode}
            size="large"
            iconSize={{ width: 24, height: 28 }}
          />
        </View>
      </View>
    </View>
  );
}

const styles = StyleSheet.create({
  container: {
    borderRadius: 8,
    backgroundColor: colors.white,
    padding: 16,
    marginBottom: 12,
  },
  layout: {
    flexDirection: 'row',
    justifyContent: 'space-between',
    alignItems: 'center',
  },
  userInfoContainer: {
    flexDirection: 'row',
    alignItems: 'center',
    flex: 1,
  },
  userTextContainer: {
    marginLeft: 12,
    flex: 1,
  },
  valueContainer: {
    alignItems: 'flex-end',
    justifyContent: 'center',
    minWidth: 120,
  },
  profileImage: {
    width: 60,
    height: 60,
    borderRadius: 30,
  },
  userName: {
    fontSize: 18,
    color: colors.gray700,
    fontWeight: '500',
  },
  userId: {
    fontSize: 14,
    color: colors.gray500,
    marginTop: 4,
  },
  pendingText: {
    fontSize: 12,
    color: colors.gray700,
    marginBottom: 4,
    fontStyle: 'italic',
  },
});

export default ChistHistoryHeader;
