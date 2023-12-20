import React from "react";
import {
  View,
  TextInput,
  StyleSheet,
  TouchableOpacity,
} from "react-native";
import { useSelector } from "react-redux";

import Avatar from "../../components/Avatar";
import { colors } from "../../config/constants";
import HelpText from "../../components/HelpText";

import {
  SwapIcon,
  UpArrowIcon,
  DownArrowIcon,
  LeftArrowIcon,
  RightArrowIcon,
} from "../../components/SvgAssets/SvgAssets";

const TallyReviewView = (props) => {
  const { imagesByDigest } = useSelector((state) => state.avatar);
  const partDigest = props.partCert?.file?.[0]?.digest;
  const holdDigest = props.holdCert?.file?.[0]?.digest;
  const tallyType = props.tallyType;
  const partImage = imagesByDigest[partDigest];
  const holdImage = imagesByDigest[holdDigest];
  const holdLimit = props.holdTerms?.limit;
  const partLimit = props.partTerms?.limit;
  const canEdit = props.canEdit ?? true;

  const onSwitchClick = () => {
    props.setTallyType((prev) => {
      const switchTally = {
        foil: "stock",
        stock: "foil",
      };

      return switchTally[prev];
    });
  };

  const getStockText = () => {
    if (tallyType === "stock") {
      if (holdImage) {
        return "Stock";
      }
    } else {
      if (partImage) {
        return "Stock";
      }
    }

    return props.holdCert.chad.cid
      ? props.holdCert.chad.cid
      : props.partCert.chad.cid;
  };

  const getFoilText = () => {
    if (tallyType === "foil") {
      if (holdImage) {
        return "Foil";
      }
    } else {
      if (partImage) {
        return "Foil";
      }
    }

    return props.holdCert.chad.cid
      ? props.holdCert.chad.cid
      : props.partCert.chad.cid;
  };

  const getCID = () => {
    if (props.holdCert.chad.cid) {
      return (
        props.holdCert.chad.cid + ":" + props.holdCert.chad.agent
      );
    }

    return props.partCert.chad.cid + ":" + props.holdCert.chad.agent;
  };

  return (
    <View style={styles.main}>
      <View style={styles.rowWrapper}>
        <View style={styles.leftIcon}>
          <HelpText
            label="Risk"
            style={[styles.leftText, styles.leftTopText]}
          />
          <DownArrowIcon />
        </View>

        <View style={styles.topCenterWrapper}>
          <HelpText
            helpText={getCID()}
            label={getFoilText()}
            style={styles.headerText}
          />

          {tallyType === "foil"
            ? holdImage && (
                <View style={styles.circle}>
                  <Avatar style={styles.circle} avatar={holdImage} />
                </View>
              )
            : partImage && (
                <View style={styles.circle}>
                  <Avatar style={styles.circle} avatar={partImage} />
                </View>
              )}
        </View>

        <View style={styles.rightIcon}>
          <HelpText
            label="Credit"
            style={[styles.rightText, styles.rightTopText]}
          />
          <LeftArrowIcon />
        </View>
      </View>

      <View style={styles.midView}>
        <View style={styles.rowWrapper}>
          <TextInput
            editable={canEdit}
            value={tallyType === "foil" ? holdLimit : partLimit}
            keyboardType="numeric"
            style={styles.input}
            onChangeText={
              tallyType === "foil"
                ? props.onHoldTermsChange("limit")
                : props.onPartTermsChange("limit")
            }
          />

          <HelpText
            helpText="help"
            label="Limit"
            style={styles.midText}
          />

          <TextInput
            editable={canEdit}
            value={tallyType === "stock" ? holdLimit : partLimit}
            keyboardType="numeric"
            style={styles.input}
            onChangeText={
              tallyType === "stock"
                ? props.onHoldTermsChange("limit")
                : props.onPartTermsChange("limit")
            }
          />
        </View>
      </View>

      <View style={styles.rowWrapper}>
        <View style={styles.leftIcon}>
          <RightArrowIcon />
          <HelpText
            label="Credit"
            style={[styles.leftText, styles.leftBottomText]}
          />
        </View>

        <View style={styles.bottomCenterWrapper}>
          {tallyType === "stock"
            ? holdImage && (
                <View style={styles.circle}>
                  <Avatar style={styles.circle} avatar={holdImage} />
                </View>
              )
            : partImage && (
                <View style={styles.circle}>
                  <Avatar style={styles.circle} avatar={partImage} />
                </View>
              )}

          <HelpText
            helpText={getCID()}
            label={getStockText()}
            style={styles.headerText}
          />
        </View>

        <View style={styles.rightIcon}>
          <UpArrowIcon />
          <HelpText
            label="Risk"
            style={[styles.rightText, styles.rightBottomText]}
          />
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
    //marginTop: 20,
    paddingTop: 20,
    marginHorizontal: 40,
    alignItems: "center",
  },
  circle: {
    height: 80,
    width: 80,
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
    marginTop: 10,
    fontWeight: "400",
    textAlign: "center",
    color: colors.dimgray,
  },
  bottomCenterWrapper: {
    height: 100,
    alignItems: "center",
    justifyContent: "center",
  },
  topCenterWrapper: {
    height: 100,
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
    width: "30%",
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
    marginBottom: -20,
    width: "50%",
  },
  leftBottomText: {
    marginTop: -20,
    width: "70%",
  },
  rightTopText: {
    marginBottom: -20,
    width: "70%",
  },
  rightBottomText: {
    marginTop: -18,
    width: "50%",
  },
  absoluteView: {
    top: 0,
    right: -20,
    position: "absolute",
  },
});

export default TallyReviewView;
