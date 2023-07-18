import React from "react";
import { ScrollView, StyleSheet, Text, View } from "react-native";
import { colors } from "../../../config/constants";

const ChitDetail = (props) => {
  const params = props.route.params;

  console.log("PROPS ==> ", props);

  return <ScrollView
    style={styles.container}
    contentContainerStyle={styles.contentContainer}
  >
    <Text style={styles.text}>CHIT IDX: {params.chit_idx}</Text>
    <Text style={styles.text}>CHIT UUID: {params.chit_uuid}</Text>
    <Text style={styles.text}>CHIT ENT: {params.chit_ent}</Text>

    <Text style={[styles.text, { color: colors.blue, fontWeight: 'bold' }]}> WORK IN PROGRESS</Text>
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
  }
})
export default ChitDetail;