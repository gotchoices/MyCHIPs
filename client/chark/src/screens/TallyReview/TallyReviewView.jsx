import React, { useEffect, useState } from "react";
import {
  View,
  TextInput,
  StyleSheet,
  TouchableOpacity,
  Text,
} from "react-native";
import { useSelector } from "react-redux";

import Avatar from "../../components/Avatar";
import { colors } from "../../config/constants";
import HelpText from "../../components/HelpText";
import useMessageText from "../../hooks/useMessageText";

import {
  SwapIcon,
  UpArrowIcon,
  DownArrowIcon,
  LeftArrowIcon,
  RightArrowIcon,
} from "../../components/SvgAssets/SvgAssets";
import { round } from "../../utils/common";

const TallyReviewView = (props) => {
  const { imagesByDigest } = useSelector((state) => state.avatar);
  const partDigest = props.partCert?.file?.[0]?.digest;
  const holdDigest = props.holdCert?.file?.[0]?.digest;
  const tallyType = props.tallyType;
  const partImage = imagesByDigest[partDigest];
  const holdImage = imagesByDigest[holdDigest];
  const canEdit = props.canEdit ?? true;

  const holdLimit = props?.holdTerms?.limit;
  const partLimit = props?.partTerms?.limit;

  const { messageText } = useMessageText();
  const talliesMessageText = messageText?.tallies_v_me?.msg;

  const checkValidInput = (textValue) => {
    return textValue && /^[0-9]*(\.[0-9]{0,3})?$/.test(textValue);
  };

  const getValidAmount = (amount) => {
    if (parseFloat(amount) > 0) {
      return amount;
    }

    return 1.0;
  };

  const calculateAmount = (value) => {
    const amount = getValidAmount(value);

    if (amount && checkValidInput(amount)) {
      return amount;
    }

    return round(amount, 3);
  };

  const onSwitchClick = () => {
    props?.setTallyType?.((prev) => {
      const switchTally = {
        foil: "stock",
        stock: "foil",
      };

      return switchTally[prev];
    });
  };

  const getStockText = () => {
    return props.holdCert?.chad?.cid
      ? props.holdCert.chad.cid + "..."
      : props.partCert?.chad?.cid + "...";
  };

  const getFoilText = () => {
    return props.partCert?.chad?.cid
      ? props.partCert.chad.cid + "..."
      : props.holdCert?.chad?.cid + "...";
  };

  const getStockCID = () => {
    if (props.holdCert?.chad?.cid) {
      return (
        props.holdCert.chad.cid + ":" + props.holdCert?.chad?.agent
      );
    }

    return (
      props.partCert?.chad?.cid + ":" + props.partCert?.chad?.agent
    );
  };

  const getFoilCID = () => {
    if (props.partCert?.chad?.cid) {
      return (
        props.partCert?.chad?.cid + ":" + props.partCert?.chad?.agent
      );
    }

    return props.holdCert.chad.cid + ":" + props.holdCert.chad.agent;
  };

  const onBlurLimit = () => {
    if(holdLimit && holdLimit.indexOf('.') >= 0) {
      props.onHoldTermsChange("limit")(round(holdLimit, 3))
    }

    if(partLimit && partLimit.indexOf('.') >= 0) {
      props.onPartTermsChange("limit")(partLimit);
    }
  }

  return (
    <View style={styles.main}>
      <View style={styles.wrapper}>
        <View style={styles.rowWrapper}>
          <View style={styles.leftIcon}>
            <HelpText
              label={talliesMessageText?.risk?.title ?? "risk_title"}
              style={[styles.leftText, styles.leftTopText]}
            />
            <DownArrowIcon />
          </View>

          <View style={styles.topCenterWrapper}>
            <HelpText
              helpText={getStockCID()}
              label={tallyType === "foil" ? "Foil" : "Stock"}
              style={styles.headerText}
            />

            {tallyType === "foil" ? (
              holdImage ? (
                <View style={styles.circle}>
                  <Avatar style={styles.circle} avatar={holdImage} />
                </View>
              ) : (
                <Text style={styles.boldText}>{getStockText()}</Text>
              )
            ) : partImage ? (
              <View style={styles.circle}>
                <Avatar style={styles.circle} avatar={partImage} />
             </View>
            ) : (
              <Text style={styles.boldText}>{getStockText()}</Text>
            )}
          </View>

          <View style={styles.rightIcon}>
            <HelpText
              label={talliesMessageText?.credit?.title ?? "credit_title"}
              style={[styles.rightText, styles.rightTopText]}
            />
            <LeftArrowIcon />
          </View>
        </View>
      </View>

      <View style={styles.midView}>
        <View style={styles.rowWrapper}>
          <TextInput
            maxLength={9}
            placeholder={props.net ?? ""}
            editable={canEdit}
            value={tallyType === "foil" ? holdLimit : partLimit}
            keyboardType="numeric"
            style={styles.input}
            onBlur={onBlurLimit}
            onChangeText={(text) => {
              tallyType === "foil"
                ? props.onHoldTermsChange("limit")(text)
                : props.onPartTermsChange("limit")(text);

            }}
          />

          <HelpText
            helpText="help"
            label="Limit"
            style={styles.midText}
          />

          <TextInput
            maxLength={9}
            editable={canEdit}
            placeholder={props.amount ?? ""}
            value={tallyType === "stock" ? holdLimit : partLimit}
            keyboardType="numeric"
            style={styles.input}
            onBlur={onBlurLimit}
            onChangeText={(text) => {
              tallyType === "stock"
                ? props.onHoldTermsChange("limit")(text)
                : props.onPartTermsChange("limit")(text);
            }}
          />
        </View>
      </View>

      <View style={styles.wrapper}>
        <View style={styles.rowWrapper}>
          <View style={styles.leftIcon}>
            <RightArrowIcon />
            <HelpText
              label={talliesMessageText?.credit?.title ?? "credit_title"}
              style={[styles.leftText, styles.leftBottomText]}
            />
          </View>

          <View style={styles.bottomCenterWrapper}>
            <HelpText
              helpText={getFoilCID()}
              label={tallyType === "foil" ? "Stock" : "Foil"}
              style={styles.headerText}
            />

            {tallyType === "stock" ? (
              holdImage ? (
                <View style={styles.circle}>
                  <Avatar style={styles.circle} avatar={holdImage} />
                </View>
              ) : (
                <Text style={styles.boldText}>{getFoilText()}</Text>
              )
            ) : partImage ? (
              <View style={styles.circle}>
                <Avatar style={styles.circle} avatar={partImage} />
              </View>
            ) : (
              <Text style={styles.boldText}>{getFoilText()}</Text>
            )}
          </View>

          <View style={styles.rightIcon}>
            <UpArrowIcon />
            <HelpText
              label={talliesMessageText?.risk?.title ?? "risk_title"}
              style={[styles.rightText, styles.rightBottomText]}
            />
          </View>
        </View>
      </View>

      {canEdit && (
        <View style={styles.absoluteView}>
          <TouchableOpacity onPress={onSwitchClick}>
            <SwapIcon />
          </TouchableOpacity>
        </View>
      )}
    </View>
  );
};

const arrowText = {
  color: "black",
  fontSize: 12,
  fontWeight: "500",
};

const styles = StyleSheet.create({
  main: {
    flex: 1,
    paddingTop: 20,
    marginHorizontal: 40,
    alignItems: "center",
  },
  circle: {
    height: 70,
    width: 70,
    borderRadius: 50,
    backgroundColor: colors.gray700,
  },
  headerText: {
    paddingTop: 10,
    fontWeight: "400",
    textAlign: "center",
    color: colors.dimgray,
  },
  midText: {
    fontWeight: "400",
    textAlign: "center",
    color: colors.dimgray,
  },
  bottomCenterWrapper: {
    height: 100,
    marginBottom: -25,
    alignItems: "center",
    justifyContent: "center",
  },
  topCenterWrapper: {
    height: 100,
    marginTop: -75,
    alignItems: "center",
    justifyContent: "center",
  },
  rowWrapper: {
    flexDirection: "row",
    alignItems: "center",
    justifyContent: "space-between",
  },
  midView: {
    marginRight: 40,
  },
  input: {
    width: "33%",
    //height: 24,
    padding: 10,
    borderRadius: 5,
    borderWidth: 0.5,
    marginHorizontal: 30,
    borderColor: colors.dimgray,
  },
  leftIcon: {
    width: "30%",
    marginLeft: 20,
    alignItems: "center",
    justifyContent: "center",
  },
  rightIcon: {
    width: "30%",
    marginRight: 20,
    alignItems: "center",
    justifyContent: "center",
  },
  leftText: {
    ...arrowText,
    marginRight: 50,
  },
  rightText: {
    ...arrowText,
    marginLeft: 50,
  },
  leftTopText: {
    marginLeft: -10,
    marginBottom: -20,
    width: "55%",
  },
  leftBottomText: {
    marginLeft: -10,
    marginTop: -20,
    width: "80%",
  },
  rightTopText: {
    marginRight: -25,
    marginBottom: -20,
    width: "80%",
  },
  rightBottomText: {
    marginRight: -25,
    marginTop: -18,
    width: "55%",
  },
  absoluteView: {
    top: 0,
    right: -20,
    position: "absolute",
  },
  boldText: {
    fontWeight: "700",
    fontSize: 15,
    textDecorationStyle: "solid",
    textDecorationLine: "underline",
  },
  wrapper: {
    height: 100,
    alignItems: "center",
    justifyContent: "center",
  },
});

export default TallyReviewView;
