import React, { useEffect, useMemo, useState } from "react";
import { StyleSheet, FlatList, View, Text, Image, ActivityIndicator } from "react-native";
import useSocket from "../../../hooks/useSocket";
import mychips from '../../../../assets/mychips-large.png';
import mychipsNeg from '../../../../assets/mychips-red-large.png';
import { fetchChitHistory } from "../../../services/tally";
import { round } from "../../../utils/common";
import moment from 'moment';
import ChistHistoryHeader from "./ChitHistoryHeader";
import { colors } from "../../../config/constants";

const ChitHistory = (props) => {
  const { tally_seq, tally_ent, tally_uuid } = props.route?.params ?? {};
  const { wm } = useSocket();

  const [loading, setLoading] = useState(true);
  const [chits, setChits] = useState(undefined);

  const totalNet = useMemo(() => {
    return chits?.reduce((total, item) => total + item.net, 0);
  }, [chits])

  useEffect(() => {
    _fetchChitHistory();
  }, [tally_uuid])

  const _fetchChitHistory = () => {
    fetchChitHistory(
      wm,
      {
        fields: ['part_cid', 'chit_ent', 'chit_idx', 'chit_uuid', 'chit_seq', 'chit_type', 'issuer', 'net', 'crt_date', 'chit_date', 'reference', 'memo', 'status'],
        order: ['crt_date'],
        where: {
          tally_uuid: tally_uuid,
        }
      }
    ).then(data => {
      if (data?.length) {
        setChits(data);
      }
    }).catch(ex => {
      console.log("EXCEPTION ==> ", ex);
    }).finally(() => {
      setLoading(false);
    });
  }

  const ChitItem = ({ item }) => {
    const isNetNegative = item?.net < 0;
    const net = round((item?.net ?? 0) / 1000, 3);
    const formatedDate = moment(item.chit_date).format('MMM DD, YYYY - hh:mm a');

    return <View style={styles.chitItem}>
      <View>
        <Text style={{ color: 'black' }}>Reference: {item.reference ?? 'not added'} </Text>
        <Text style={{ color: 'black' }}>Memo: {item.memo ?? 'not added'}</Text>
        <Text style={{ color: 'black' }}>Status: {item.status}</Text>
        <Text style={[styles.label, { marginTop: 4 }]}>{formatedDate}</Text>
      </View>
      <View style={isNetNegative ? styles.debidBg : styles.creditBg}>
        <Image source={isNetNegative ? mychipsNeg : mychips} style={styles.image} resizeMode='contain' />
        <Text style={isNetNegative ? styles.negativeText : styles.positiveText}>
          {net}
        </Text>
      </View>
    </View>
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
      ListHeaderComponent={
        <ChistHistoryHeader
          args={{
            ...props.route?.params,
            runningBalance: totalNet
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
    flexDirection: 'row',
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