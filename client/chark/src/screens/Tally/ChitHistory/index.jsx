import React, { useEffect, useState, useMemo } from "react";
import { useSelector } from 'react-redux';
import { StyleSheet, FlatList, View, Text, Image, ActivityIndicator, TouchableOpacity, RefreshControl } from "react-native";

import useSocket from "../../../hooks/useSocket";
import mychips from '../../../../assets/mychips-large.png';
import mychipsNeg from '../../../../assets/mychips-red-large.png';
import { fetchChitHistory } from "../../../services/tally";
import { round } from "../../../utils/common";
import ChistHistoryHeader from "./ChitHistoryHeader";
import { colors, dateFormats } from "../../../config/constants";
import { ChitIcon } from "../../../components/SvgAssets/SvgAssets";
import { formatDate } from "../../../utils/format-date";

const ChitHistory = (props) => {
  const { tally_uuid, digest } = props.route?.params ?? {};
  const { wm } = useSocket();
  const [loading, setLoading] = useState(true);
  const [chits, setChits] = useState(undefined);
  const { imagesByDigest } = useSelector((state) => state.avatar);
  const avatar = imagesByDigest?.[digest];

  useEffect(() => {
    _fetchChitHistory();
  }, [tally_uuid])

  const _fetchChitHistory = () => {
    setLoading(true);
    fetchChitHistory(
      wm,
      {
        fields: [
          'part_cid', 'chit_ent', 'chit_idx', 'chit_uuid', 'chit_seq', 'chit_type', 'issuer', 'net', 
          'crt_date', 'chit_date', 'reference', 'memo', 'status', 'state', 'chain_idx', 'action'
        ],
        where: {
          tally_uuid: tally_uuid,
        },
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
    const net = round((item?.net ?? 0) / 1000, 3);
    const isNetNegative = net < 0;

    const runningBalance = round((item?.runningBalance ?? 0) / 1000, 3);
    const isRunningBalnceNeg = runningBalance < 0;

    const formatedDate = formatDate({ date: item.chit_date, format: dateFormats.dateTime });

    return <TouchableOpacity
      style={styles.chitItem}
      onPress={() => { onChipClick(item, index) }}
    >
      <View>
        {
          item?.action && <View style={{ backgroundColor: 'red', width: "100%", paddingHorizontal: 12, paddingVertical: 4, borderRadius: 12 }}>
            <Text style={{ color: 'white', fontSize: 12 }}>Action Required</Text>
          </View>
        }
      </View>
      <View style={{ ...styles.chitItem, flexDirection: 'row' }}>
        <View style={{ flex: 1 }}>
          <Text style={[styles.label, { marginTop: 6 }]}>{formatedDate}</Text>

          <View style={{ flexDirection: 'row', alignItems: 'center', marginTop: 12 }}>
            <Text style={{ color: 'black' }}>Running Balance:  </Text>
            <View style={styles.row}>
              <Image source={isRunningBalnceNeg ? mychipsNeg : mychips} style={styles.image} resizeMode='contain' />
              <Text style={isRunningBalnceNeg ? styles.negativeText : styles.positiveText}>{runningBalance}</Text>
            </View>
          </View>

          <Text style={{ color: 'black', marginTop: 4 }}>Reference: {JSON.stringify(item.reference) ?? 'not added'} </Text>
          <Text style={{ color: 'black', marginTop: 4 }}>Memo: {item.memo ?? 'not added'}</Text>
          <Text style={{ color: 'black', marginTop: 4 }}>State: {item.state}</Text>
          <Text style={{ color: 'black', marginTop: 4 }}>Action: {item.action?.toString()}</Text>
        </View>

        <View style={{ width: 8 }} />
        <View style={isNetNegative ? styles.debidBg : styles.creditBg}>
          <ChitIcon color={isNetNegative ? colors.red : colors.green} height={14} width={14} />
          <Text style={isNetNegative ? styles.negativeText : styles.positiveText}>
            {net}
          </Text>
        </View>
      </View>
    </TouchableOpacity >
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
    padding: 12,
    alignItems: 'flex-start',
    borderRadius: 8,
    justifyContent: 'space-between'
  },
  row: {
    flexDirection: 'row',
    justifyContent: 'center',
    alignItems: 'center'
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
    height: 12,
  },
  label: {
    color: colors.gray500,
    fontSize: 12,
  },
  creditBg: {
    backgroundColor: '#EEF2F5',
    borderRadius: 30,
    paddingHorizontal: 8,
    paddingVertical: 4,
    flexDirection: 'row',
    alignItems: 'center',
    justifyContent: 'center'
  },
  debidBg: {
    backgroundColor: "#FEF0EF",
    borderRadius: 30,
    paddingHorizontal: 8,
    paddingVertical: 4,
    flexDirection: 'row',
    alignItems: 'center',
    justifyContent: 'center'
  }
});

export default ChitHistory;
