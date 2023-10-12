import React from "react";
import { View, StyleSheet, Text, Dimensions } from "react-native";
import { useSelector } from "react-redux";

import { colors } from "../../../config/constants";
import useMessageText from "../../../hooks/useMessageText";

import Header from "../Header";
import Avatar from "../../../components/Avatar";
import {
  ChitIcon,
  NotificationIcon,
  VisualIcon,
} from "../../../components/SvgAssets/SvgAssets";

const Banner = (props) => {
  const { avatar, personal } = useSelector((state) => state.profile);
  const { messageText } = useMessageText();
  const userTallyText = messageText?.userTallies ?? {};

  const navigateToReport = () => {
    props.navigation?.navigate?.("TallyReport");
  };

  const isNetNegative = props.totalNet < 0;

  return (
    <View style={styles.container}>
      <Header
        leftIcon={<VisualIcon />}
        title="My CHIPs"
        onClick={navigateToReport}
        rightIcon={<NotificationIcon />}
      />

      <View style={{ alignItems: "center", justifyContent: "center" }}>
        <View style={styles.balanceContainer}>
          <View style={styles.balance}>
            <View style={styles.avatarWrapper}>
              <Avatar avatar={avatar} />
              <Text style={styles.name}>{personal?.cas_name ?? ""}</Text>
            </View>
          </View>
        </View>
      </View>

      <View style={styles.textWrapper}>
        {!!props.currencyCode && (
          <Text style={styles.amount}>
            {props.totalNetDollar} {props.currencyCode}
          </Text>
        )}

        <View style={{ flexDirection: "row", alignItems: "center" }}>
          <ChitIcon color={isNetNegative ? colors.red : colors.green} />
          <Text
            style={isNetNegative ? styles.mychipsNetNeg : styles.mychipsNet}
          >
            {props.totalNet}
          </Text>
        </View>
      </View>
    </View>
  );
};

const mychipsNet = {
  marginLeft: 5,
  fontSize: 32,
  fontWeight: "500",
  color: colors.green,
  maxWidth: Dimensions.get("window").width * 0.5,
};

const styles = StyleSheet.create({
  container: {
    marginHorizontal: 10,
  },
  balanceContainer: {
    padding: 16,
    maxWidth: "90%",
    borderRadius: 25,
    overflow: "hidden",
  },
  balance: {
    flexDirection: "row",
    alignItems: "center",
    justifyContent: "space-between",
  },
  mychipsNet,
  mychipsNetNeg: {
    ...mychipsNet,
    color: colors.red,
  },
  name: { paddingTop: 15, fontSize: 16, fontWeight: "600" },
  avatarWrapper: { marginTop:20},
  textWrapper: {
    marginBottom:-15,
    marginRight: 10,
    alignItems: "flex-end",
    justifyContent: "flex-end",
  },
  amount: {
    fontSize: 16,
    color: colors.gray300,
  },
});

export default Banner;
