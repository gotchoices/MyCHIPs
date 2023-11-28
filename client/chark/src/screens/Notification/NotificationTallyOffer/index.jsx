import React from "react";
import { View, Text, StyleSheet } from "react-native";

import Avatar from "../../../components/Avatar";
import { colors } from "../../../config/constants";

const NotificationTallyOffer = (props) => {
  // Dummy data used for UI Purpose - needs discussion

  return (
    <View style={styles.main}>
      <View style={styles.container}>
        <Avatar style={styles.avatar} avatar={props.image} />

        <View style={{ flex: 1 }}>
          <Text style={styles.name}>Jason Bourne</Text>
          <Text style={[styles.description, { marginTop: 5 }]}>
            Sent you a tally offer
          </Text>
        </View>
      </View>
      <View style={styles.price}>
        <Text style={[styles.description]}>09/02/23</Text>
      </View>
    </View>
  );
};

const styles = StyleSheet.create({
  main: {
    height: 50,
    flexDirection: "row",
    justifyContent: "space-between",
  },
  container: {
    flex: 1,
    flexDirection: "row",
    alignItems: "center",
    justifyContent: "space-between",
  },
  avatar: {
    width: 55,
    height: 55,
    marginRight: 8,
    alignSelf: "center",
    borderRadius: 55 / 2,
  },
  name: {
    fontSize: 16,
    fontWeight: "bold",
  },
  price: {
    alignItems: "flex-end",
    justifyContent: "flex-start",
  },
  myChips: {
    flexDirection: "row",
    alignItems: "center",
  },
  description: {
    fontSize: 12,
    color: colors.gray500,
  },
  text: {
    fontSize: 10,
  },
});

export default NotificationTallyOffer;
