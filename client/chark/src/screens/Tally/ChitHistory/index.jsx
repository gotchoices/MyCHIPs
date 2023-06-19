import React, { useEffect, useState } from "react";
import { StyleSheet, FlatList, View, Text, Image, ActivityIndicator } from "react-native";
import useSocket from "../../../hooks/useSocket";
import mychips from '../../../../assets/mychips-large.png';
import mychipsNeg from '../../../../assets/mychips-red-large.png';
import { fetchChitHistory } from "../../../services/tally";

const ChitHistory = (props) => {
  const { tally_seq, tally_ent } = {}//props.route?.params ?? {};
  const { wm } = useSocket();

  const [loading, setLoading] = useState(true);
  const [chits, setChits] = useState(undefined);

  useEffect(() => {
    _fetchChitHistory();
  }, [tally_seq, tally_ent])

  const _fetchChitHistory = () => {
    fetchChitHistory(
      wm,
      {
        fields: ['chit_ent', 'chit_idx', 'chit_uuid', 'chit_seq', 'chit_type', 'issuer', 'net', 'crt_date', 'chit_date'],
        order: ['crt_date'],
      }
    ).then(data => {
      if (data?.length) {
        setChits(data);
      }
    }).finally(() => {
      setLoading(false);
    });
  }

  const ChitItem = ({ item }) => {
    const isNetNegative = item?.net < 0;

    return <View style={styles.chitItem}>
      <View style={styles.container}>
        <Text style={styles.title}>{item.chit_date}</Text>
        <Text style={styles.body} numberOfLines={1} ellipsizeMode="middle">Chit Id: {item.chit_uuid}</Text>
        <Text style={styles.body}>Chit Ent: {item.chit_ent}</Text>
        <Text style={styles.body}>Chit Seq: {item.chit_seq}</Text>
        <Text style={styles.body}>Chit Type: {item.chit_type}</Text>
        <Text style={styles.body}>Issuer: {item.issuer}</Text>
      </View>

      <View style={styles.row}>
        <Image source={isNetNegative ? mychipsNeg : mychips} style={styles.image} resizeMode='contain' />
        <Text style={isNetNegative ? styles.negativeText : styles.positiveText}>
          {item.net}
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
      contentContainerStyle={styles.contentContainer}
      data={chits}
      renderItem={ChitItem}
      keyExtractor={item => item.chit_uuid.toString()}
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
    padding: 8
  },
  chitItem: {
    flexDirection: 'row',
    backgroundColor: 'white',
    padding: 12,
    alignItems: 'flex-start'
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
    fontSize: 16,
    fontWeight: 'bold',
    color: 'black'
  },
  body: {
    fontSize: 14,
    color: 'black',
  },
  spacer: {
    height: 12,
  }
});

export default ChitHistory;