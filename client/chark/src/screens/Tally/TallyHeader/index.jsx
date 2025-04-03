import React from "react";
import { View, StyleSheet } from "react-native";
import Banner from "../Banner";
import Search from "../Search";

const TallyHeader = (props) => {
  return <View>
    <Banner
      totalNet={props.totalNet}
      totalNetUnits={props.totalNetUnits}
      totalPendingNet={props.totalPendingNet}
      totalNetDollar={props.totalNetDollar}
      navigation={props.navigation}
      currencyCode={props.currencyCode}
    />

    <View style={styles.search}>
      <Search  searchInput ={(text)=>props.searchInput(text)}/>
    </View>
  </View>
}

const styles = StyleSheet.create({
  search: {
    marginTop: 16,
    backgroundColor: '#fff',
    paddingHorizontal: 24,
    paddingVertical: 16,
    marginBottom: 16,
  }
})

export default TallyHeader;
