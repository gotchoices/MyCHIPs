import React, { useEffect } from "react"
import { ScrollView, StyleSheet, Text, View } from "react-native"

const TallyCertificate = (props) => {
  const { data } = props.route?.params ?? {};

  useEffect(() => {
    props.navigation.setOptions({
      title: data?.title ?? "Tally Certificate",
    });
  }, []);

  return <ScrollView style={styles.container}>
    <Text>{JSON.stringify(data?.data, null, 2)}</Text>
  </ScrollView>
}

const styles = StyleSheet.create({
  container: {
    padding: 16,
    margin: 16,
    backgroundColor: 'white'
  }
})

export default TallyCertificate;