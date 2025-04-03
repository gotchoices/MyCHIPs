import React, { useMemo } from "react";
import { StyleSheet, Text, View } from "react-native"

import { colors } from "../../../../config/constants";
import Avatar from "../../../../components/Avatar";
import ChipValue from "../../../../components/ChipValue";
import useMessageText from "../../../../hooks/useMessageText";

const ChistHistoryHeader = (props) => {
  const { part_name, cuid, net, wm, avatar, net_pc } = props.args ?? {};
  const { messageText } = useMessageText();
  const chitMeText = messageText?.chits_v_me?.col;

  const pendingText = useMemo(() => {
    return chitMeText?.status?.values?.find(s => s.value === 'pend');
  }, [chitMeText?.status?.values])

  // Check if there's a pending amount (difference between pending and current)
  const hasPendingAmount = useMemo(() => {
    if (net_pc !== undefined && net !== undefined) {
      const pendingValue = Number(net_pc);
      const currentValue = Number(net);
      const difference = pendingValue - currentValue;
      
      // Only return true if there's a non-zero difference
      return difference !== 0;
    }
    return false;
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
          {hasPendingAmount && (
            <View style={styles.pendingContainer}>
              <Text style={styles.pendingText}>
                {pendingText?.title ?? 'Pending'}:
              </Text>
              <ChipValue 
                units={net_pc - net}
                size="small"
                showCurrency={false}
              />
            </View>
          )}
          
          {/* Tally total */}
          <ChipValue 
            units={net ?? 0}
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
  pendingContainer: {
    flexDirection: 'row',
    alignItems: 'center',
    marginBottom: 6,
  },
  pendingText: {
    fontSize: 12,
    color: colors.gray700,
    fontStyle: 'italic',
    marginRight: 4,
  },
});

export default ChistHistoryHeader;
