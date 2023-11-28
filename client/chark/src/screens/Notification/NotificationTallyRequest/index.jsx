import React from "react";
import { View, Text, StyleSheet } from "react-native";

import Avatar from "../../../components/Avatar";
import Button from "../../../components/Button";
import { colors } from "../../../config/constants";

const NavigationTallyRequest = (props) => {
  // Dummy data used for UI Purpose - needs discussion

  const ActionView = () => {
    return (
      <View style={styles.price}>
        <Text style={[styles.description, { marginBottom: 5 }]}>45 min</Text>

        <View style={styles.buttonView}>
          <Button
            textStyle={styles.text}
            textColor="blue"
            title="Reject"
            onPress={() => {}}
            style={styles.secondaryButton}
          />

          <Button
            textStyle={styles.text}
            title="Accept"
            onPress={() => {}}
            style={styles.button}
          />
        </View>
      </View>
    );
  };

  return (
    <View style={styles.container}>
      <Avatar style={styles.avatar} avatar={props.image} />

      <View style={{ flex: 1 }}>
        <Text style={styles.name}>Harold Law</Text>
        <Text style={[styles.description, { marginTop: 4 }]}>
          Tally Request
        </Text>
      </View>

      <ActionView />
    </View>
  );
};

const myChipsNet = {
  fontSize: 18,
  paddingBottom: 3,
  fontWeight: "600",
  color: colors.green,
};

const styles = StyleSheet.create({
  button: {
    width:50,
    height: 25,
    marginBottom: 3,
    borderRadius: 40,
    paddingVertical: 0,
    borderColor: "blue",
    alignItems: "center",
    backgroundColor: "blue",
    justifyContent: "center",
  },
  secondaryButton: {
    height: 23,
    width:50,
    marginBottom: 3,
    borderRadius: 40,
    paddingVertical: 0,
    borderColor: "blue",
    alignItems: "center",
    backgroundColor: "white",
    justifyContent: "center",
  },
  container: {
    height: 50,
    flexDirection: "row",
    alignItems: "center",
    justifyContent: "space-between",
  },
  profile: {
    flexDirection: "row",
  },
  avatar: {
    marginRight: 8,
    alignSelf: "center",
    height: 55,
    width: 55,
    borderRadius: 55 / 2,
  },
  name: {
    fontSize: 16,
    fontWeight: "bold",
  },
  description: {
    fontSize: 12,
    color: colors.gray500,
  },
  price: {
    alignItems: "flex-end",
  },
  myChips: {
    flexDirection: "row",
    alignItems: "center",
  },
  myChipsNet,
  myChipsNetNeg: {
    ...myChipsNet,
    color: colors.red,
  },
  dollar: {
    color: colors.green,
    fontSize: 10,
    fontWeight: "600",
  },
  dollarNeg: {
    color: colors.red,
    fontSize: 10,
    fontWeight: "600",
  },
  buttonView: {
    marginLeft: 10,
  },
  text: {
    fontSize: 10,
  },
});

export default NavigationTallyRequest;
