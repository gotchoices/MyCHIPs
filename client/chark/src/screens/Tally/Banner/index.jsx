import React from "react";
import {
  View,
  Text,
  StyleSheet,
  Dimensions,
  TouchableOpacity,
} from "react-native";
import { useSelector } from "react-redux";

import { colors } from "../../../config/constants";
import { isNil } from "../../../utils/common";
import useMessageText from "../../../hooks/useMessageText";

import Header from "../Header";
import Avatar from "../../../components/Avatar";
import {
  ChitIcon,
  FilterSecondIcon,
  NotificationIcon,
  VisualIcon,
} from "../../../components/SvgAssets/SvgAssets";

const Banner = (props) => {
  const { avatar, personal } = useSelector((state) => state.profile);
  const { messageText } = useMessageText();

  const navigateToReport = () => {
    props.navigation?.navigate?.("TallyReport");
  };

  const navigateToNotification = () => {
    props.navigation?.navigate?.("Activity");
  };

  const isNetNegative = props.totalNet < 0;
  const hasPendingTotal =
    !isNil(props.totalPendingNet) && 
    (
      props.totalPendingNet != 0.0 &&
      props.totalPendingNet != props.totalNet // If pending net and total net are equal, then the tally does not have pending chits
    );

    const onFilter = () => {
      props.navigation.navigate("FilterTallyScreen");
    };

  return (
    <View style={styles.container}>
      <Header
        leftIcon={<VisualIcon />}
        title="My CHIPs"
        onClick={navigateToReport}
        onNavigateToNotification={navigateToNotification}
        rightIcon={<NotificationIcon />}
      />

      <View
        style={{ alignItems: "center", justifyContent: "center" }}
      >
        <View style={styles.balanceContainer}>
          <View style={styles.balance}>
            <View style={styles.avatarWrapper}>
              <Avatar avatar={avatar} />
              <Text style={styles.name}>
                {personal?.cas_name ?? ""}
              </Text>
            </View>
          </View>
        </View>
      </View>

      <View style={styles.row}>
        <TouchableOpacity
          style={styles.filterContainer}
          onPress={onFilter}
        >
          <FilterSecondIcon />
          <Text style={styles.filterText}>Filters</Text>
        </TouchableOpacity>

        <View style={styles.textWrapper}>
          {hasPendingTotal && (
            <Text style={styles.pending}>
              {props.totalPendingNet} pending
            </Text>
          )}

          <View
            style={{ flexDirection: "row", alignItems: "center" }}
          >
            <ChitIcon
              color={isNetNegative ? colors.red : colors.green}
            />
            <Text
              style={
                isNetNegative
                  ? styles.mychipsNetNeg
                  : styles.mychipsNet
              }
            >
              {props.totalNet}
            </Text>
          </View>

          {!!props.currencyCode && (
          <Text style={styles.amount}>
            {props.totalNetDollar} {props.currencyCode}
          </Text>
        )}
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
  fontFamily: "inter",
};

const font = {
  fontFamily: "inter",
};

const styles = StyleSheet.create({
  container: {
    marginHorizontal: 10,
  },
  balanceContainer: {
    ...font,
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
  name: { ...font, paddingTop: 15, fontSize: 16, fontWeight: "600" },
  avatarWrapper: { marginTop: 20 },
  textWrapper: {
    marginBottom: -15,
    marginRight: 10,
    alignItems: "flex-end",
    justifyContent: "flex-end",
  },
  amount: {
    ...font,
    fontSize: 16,
    color: colors.gray300,
  },
  pending: {
    ...font,
    fontSize: 12,
  },
  filterContainer: {
    height: 30,
    borderWidth: 1,
    borderRadius: 20,
    paddingVertical: 3,
    flexDirection: "row",
    alignItems: "center",
    paddingHorizontal: 12,
    justifyContent: "center",
    borderColor: colors.white100,
    backgroundColor: colors.white200,
  },
  filterText: {
    fontSize: 12,
    marginStart: 4,
    color: "#636363",
    fontFamily: "inter",
  },
  row:{
    marginLeft:10,
    flexDirection:'row',
    alignItems:'flex-end',
    justifyContent:'space-between'
  }
});

export default Banner;
