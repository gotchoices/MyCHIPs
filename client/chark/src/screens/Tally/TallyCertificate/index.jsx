import React, { useEffect } from "react"
import { ScrollView, StyleSheet, Text, View } from "react-native"

const renderKeyValue = (data) => {
  return Object.keys(data).map((key) => {
    const value = data[key];
    return (
      <View key={key} style={styles.row}>
        <Text style={styles.title}>{key}: </Text>
        <Text style={styles.subtitle}>{JSON.stringify(value, null, 2)}</Text>
      </View>
    );
  });
};

const TallyCertificate = (props) => {
  const { data } = props.route?.params ?? {};

  useEffect(() => {
    console.log("DATA ==> ", JSON.stringify(data?.data));
    props.navigation.setOptions({
      title: data?.title ?? "Tally Certificate",
    });
  }, []);

  return <ScrollView
    style={styles.container}
    contentContainerStyle={styles.contentContainer}
  >
    {renderKeyValue(data?.data)}
  </ScrollView>
}

const styles = StyleSheet.create({
  container: {
    flex: 1,
  },
  contentContainer: {
    padding: 16,
    margin: 16,
    backgroundColor: 'white'
  },
  title: {
    fontSize: 22,
    fontWeight: 'bold',
    marginVertical: 5,
  },
  subtitle: {
    fontSize: 16,
    marginVertical: 3,
  },
  row: {
    flexDirection: 'row'
  }
});

export default TallyCertificate;