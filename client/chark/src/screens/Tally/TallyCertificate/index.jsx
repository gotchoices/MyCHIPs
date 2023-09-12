import React, { useEffect } from "react"
import { ScrollView, StyleSheet, Text, View } from "react-native"
import { colors } from "../../../config/constants";

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
    {
      Object.keys(data?.data).map((key) => {
        const detail = data?.data?.[key];
        if (Array.isArray(detail) && detail.length !== 0) {
          return <View>
            <Text style={styles.title}>{key}</Text>
            {
              detail?.map((item) => {
                return <Text style={styles.subtitle}>{JSON.stringify(item)}</Text>
              })
            }
          </View>
        }
        return <View>
          <Text style={styles.title}>{key}</Text>
          <Text style={styles.subtitle}>{JSON.stringify(detail)}</Text>
        </View>
      })
    }
    {/* {renderKeyValue(data?.data)} */}
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
    paddingHorizontal: 6,
    paddingVertical: 8,
    backgroundColor: colors.gray700,
    color: colors.white,
  },
  subtitle: {
    fontSize: 16,
    marginVertical: 3,
    paddingHorizontal: 6,
    paddingVertical: 8,
    backgroundColor: colors.gray100,
    marginBottom: 6,
  },
  row: {
    flexDirection: 'row'
  }
});

export default TallyCertificate;