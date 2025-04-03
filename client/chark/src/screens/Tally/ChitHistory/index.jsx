import React, { useEffect, useState } from "react";
import { useSelector } from 'react-redux';
import { StyleSheet, FlatList, View, Text, ActivityIndicator, TouchableOpacity, RefreshControl } from "react-native";

import useSocket from "../../../hooks/useSocket";
import { fetchChitHistory } from "../../../services/tally";
import { round, unitsToChips, unitsToFormattedChips } from "../../../utils/common";
import ChistHistoryHeader from "./ChitHistoryHeader";
import { colors, dateFormats } from "../../../config/constants";
import ChipValue from "../../../components/ChipValue";
import { formatDate } from "../../../utils/format-date";
import useMessageText from '../../../hooks/useMessageText';
import useTitle from '../../../hooks/useTitle';

const ChitHistory = (props) => {
  const { tally_uuid, digest } = props.route?.params ?? {};
  const { wm } = useSocket();
  const [loading, setLoading] = useState(true);
  const [chits, setChits] = useState(undefined);
  const { imagesByDigest } = useSelector((state) => state.avatar);
  const avatar = imagesByDigest?.[digest];
  const { messageText } = useMessageText();
  const chitMeText = messageText?.chits_v_me;

  useTitle(props.navigation, chitMeText?.msg?.chits?.title)

  useEffect(() => {
    _fetchChitHistory();
  }, [tally_uuid])

  const _fetchChitHistory = () => {
    setLoading(true);
    fetchChitHistory(
      wm,
      {
        fields: [
          'part_cuid', 'chit_ent', 'chit_idx', 'chit_uuid', 'chit_seq', 'chit_type', 'issuer', 'net', 
          'crt_date', 'chit_date', 'reference', 'memo', 'status', 'state', 'chain_idx', 'action'
        ],
        where: [
          `tally_uuid = ${tally_uuid}`,
          "status = good",
          "chit_type != set"
        ],
        order: [
          {
            field: 'action',
            asc: false,
          },
          {
            field: 'crt_date',
            asc: false,
          },
        ]
      }
    ).then(data => {
      if (data?.length) {
        let runningBalance = 0;
        const chitsWithRunningBalance = data.map((item) => {
          runningBalance += item.net;
          return { ...item, runningBalance };
        });
        setChits(chitsWithRunningBalance);
      }
    }).catch(ex => {
      console.log("EXCEPTION ==> ", ex);
    }).finally(() => {
      setLoading(false);
    });
  }

  const onChipClick = (item, index) => {
    props.navigation.navigate('ChitDetail', {
      chit_uuid: item.chit_uuid,
      chit_ent: item.chit_ent,
      chit_idx: item.chit_idx,
      chit_seq: item.chit_seq,
    });
  }

  const ChitItem = ({ item, index }) => {
    const formattedDate = formatDate({ date: item.chit_date, format: dateFormats.dateTime });
    
    // Get chit type for display
    const chitType = item.chit_type || 'lift';
    const chitTypeText = chitMeText?.col?.chit_type?.values?.find(v => v.value === chitType)?.title || chitType;
    
    // Check if reference and memo have content
    const hasReference = item.reference && 
                         item.reference !== 'null' && 
                         item.reference !== '{}' &&
                         JSON.stringify(item.reference) !== '{}';
                         
    const hasMemo = item.memo && item.memo.trim() !== '';
    
    // ChipValue component now handles currency conversion internally
    // No need to calculate conversion values here

    return (
      <TouchableOpacity
        style={styles.chitItem}
        onPress={() => { onChipClick(item, index) }}
      >
        {/* Transaction type (smaller font, left justified) */}
        <Text style={styles.transactionTypeText}>
          {chitTypeText}
        </Text>
        
        {/* Main row: Date, Amount, Total */}
        <View style={styles.mainRow}>
          {/* Date (indented) */}
          <Text style={styles.dateText}>{formattedDate}</Text>
          
          {/* Chit amount (center) */}
          <View style={styles.amountContainer}>
            <ChipValue 
              units={item?.net ?? 0}
              size="small"
              showIcon={true}
              iconSize={{width: 12, height: 12}}
            />
          </View>
          
          {/* Running balance (right) */}
          <View style={styles.balanceContainer}>
            <ChipValue 
              units={item?.runningBalance ?? 0}
              size="small"
              showIcon={false}
              iconSize={{width: 10, height: 10}}
            />
          </View>
        </View>
        
        {/* Memo and reference (if they exist) */}
        {(hasMemo || hasReference) && (
          <View style={styles.detailsContainer}>
            {hasMemo && (
              <Text style={styles.memoText} numberOfLines={2} ellipsizeMode="tail">
                {item.memo}
              </Text>
            )}
            
            {hasReference && (
              <Text style={styles.referenceText} numberOfLines={1} ellipsizeMode="tail">
                {typeof item.reference === 'string' ? item.reference : JSON.stringify(item.reference)}
              </Text>
            )}
          </View>
        )}
      </TouchableOpacity>
    );
  }

  const ItemSeparator = () => {
    return <View style={styles.spacer} />
  }

  if (loading) {
    return <View style={[styles.container, { justifyContent: "center", alignItems: 'center' }]}>
      <ActivityIndicator />
    </View>
  }

  return <View style={styles.container}>
    <FlatList
      refreshControl={
        <RefreshControl
          refreshing={loading}
          onRefresh={_fetchChitHistory}
        />
      }
      ListHeaderComponent={
        <ChistHistoryHeader
          args={{
            ...props.route?.params,
            wm,
            avatar,
          }}
        />
      }
      contentContainerStyle={styles.contentContainer}
      data={chits}
      renderItem={ChitItem}
      keyExtractor={(item, index) => `${item.chit_uuid}${index}`}
      ItemSeparatorComponent={<ItemSeparator />}
      refreshing={loading}
      onRefresh={_fetchChitHistory}
    />
  </View>
}

const styles = StyleSheet.create({
  container: {
    flex: 1
  },
  contentContainer: {
    padding: 16
  },
  chitItem: {
    backgroundColor: 'white',
    padding: 10,
    paddingBottom: 8,
    borderRadius: 8,
    overflow: 'hidden'
  },
  transactionTypeText: {
    fontSize: 10,
    color: colors.gray500,
    marginBottom: 2,
    fontStyle: 'italic'
  },
  mainRow: {
    flexDirection: 'row',
    justifyContent: 'space-between',
    alignItems: 'center',
    marginLeft: 8
  },
  dateText: {
    fontSize: 13,
    fontWeight: '500',
    color: colors.gray700,
    flex: 1
  },
  amountContainer: {
    alignItems: 'center',
    flex: 1,
    justifyContent: 'center'
  },
  balanceContainer: {
    alignItems: 'flex-end',
    justifyContent: 'flex-end',
    minWidth: 80
  },
  detailsContainer: {
    marginTop: 6,
    marginLeft: 16,
    marginRight: 8
  },
  memoText: {
    fontSize: 13,
    color: colors.black100,
    marginBottom: 3
  },
  referenceText: {
    fontSize: 11,
    color: colors.gray500,
    marginBottom: 2,
    fontStyle: 'italic'
  },
  row: {
    flexDirection: 'row',
    justifyContent: 'center',
    alignItems: 'center'
  },
  title: {
    fontSize: 14,
    fontWeight: 'bold',
    color: '#14396C'
  },
  body: {
    fontSize: 14,
    color: 'black',
  },
  spacer: {
    // Reduced spacing between items by 50%
    height: 6,
  },
  label: {
    color: colors.gray500,
    fontSize: 12,
  }
});

export default ChitHistory;
