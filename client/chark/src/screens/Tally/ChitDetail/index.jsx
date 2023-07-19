import React, { useEffect, useState } from "react";
import { ActivityIndicator, Alert, ScrollView, StyleSheet, Text, View } from "react-native";
import { colors } from "../../../config/constants";
import useSocket from "../../../hooks/useSocket";
import { fetchChitHistory } from "../../../services/tally";

const ChitDetail = (props) => {
  const { chit_uuid } = props.route.params;
  const { wm } = useSocket();
  const [chit, setChit] = useState(undefined);
  const [loading, setLoading] = useState(true);

  useEffect(() => {
    if (chit_uuid) {
      _fetchChitDetails();
    }
  }, [chit_uuid])

  const _fetchChitDetails = () => {
    fetchChitHistory(
      wm,
      {
        fields: ['chit_uuid', 'chit_seq', 'net', 'chain_idx', 'chain_hash', 'signature', 'clean'],
        where: {
          chit_uuid
        },
      }
    ).then(data => {
      if (data.length > 0) {
        setChit(data[0]);
      }
    }).catch(ex => {
      Alert.alert("Error", ex);
    }).finally(() => setLoading(false))
  }

  if (loading) {
    return <View style={styles.loadingContainer}>
      <ActivityIndicator />
    </View>
  }

  return <ScrollView
    style={styles.container}
    contentContainerStyle={styles.contentContainer}
  >
    <Text style={styles.text}>CHIT UUID: {chit?.chit_uuid}</Text>
    <Text style={styles.text}>CHAIN HASH: {chit?.chain_hash.type} {chit?.chain_hash.data.toString()}</Text>
    <Text style={styles.text}>SIGNATURE: {chit?.signature}</Text>
    <Text style={styles.text}>CLEAN: {chit?.clean.toString()}</Text>

    <Text style={[styles.text, { color: colors.blue, fontWeight: 'bold' }]}>WORK IN PROGRESS</Text>
  </ScrollView>
}


const styles = StyleSheet.create({
  container: { flex: 1 },
  contentContainer: {
    backgroundColor: colors.white,
    padding: 16,
    margin: 12,
  },
  text: {
    fontSize: 16,
    color: colors.black,
    marginVertical: 8,
  },
  loadingContainer: {
    flex: 1,
    justifyContent: 'center',
    alignItems: 'center',
  }
})
export default ChitDetail;