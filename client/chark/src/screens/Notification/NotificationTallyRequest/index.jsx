import React from "react";
import { View, Text, StyleSheet } from "react-native";

import Avatar from "../../../components/Avatar";
import Button from "../../../components/Button";
import { colors } from "../../../config/constants";
import { useSelector } from "react-redux";

const NavigationTallyRequest = (props) => {
  const { tally } = props;

  const { imagesByDigest } = useSelector((state) => state.avatar);

  const partCert = tally.part_cert;
  const digest = partCert?.file?.[0]?.digest;
  const avatar = imagesByDigest[digest];

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
      <Avatar style={styles.avatar} avatar={avatar} />

      <View style={{ flex: 1 }}>
        <Text style={styles.name}>
          {tally.part_cert?.name?.first + " " + tally.part_cert?.name?.surname}
        </Text>
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
    marginRight: 10,
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
    marginRight: -10,
    flexDirection: "row",
    alignItems: "center",
  },
  text: {
    fontSize: 10,
  },
});

export default NavigationTallyRequest;
