import React, { useState } from "react";
import { Dimensions, StyleSheet, TextInput, TouchableOpacity, View } from "react-native";

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

const TallyReviewView = () => {
  const [avatar, setAvatar] = useState("");

  const [partTerm, setPartTerm] = useState("");
  const [holdTerm, setHoldTerm] = useState("");

  const [isSwappedView, setIsSwappedView] = useState(false);

  return (
    <View style={styles.main}>
      <View style={styles.rowWrapper}>
        <View style={styles.leftIcon}>
          <HelpText label="Risk" style={styles.leftText} />
          <DownArrowIcon />
        </View>

        <>
          {isSwappedView ? (
            <View style={styles.topCenterWrapper}>
              <HelpText
                helpText="help"
                label="Stock"
                style={styles.headerText}
              />

              <View style={styles.circle}>
                <Avatar style={styles.circle} avatar={avatar} />
              </View>
            </View>
          ) : (
            <View style={styles.topCenterWrapper}>
              <HelpText
                helpText="help"
                label="Foil"
                style={styles.headerText}
              />

              <View style={styles.circle}>
                <Avatar style={styles.circle} avatar={avatar} />
              </View>
            </View>
          )}
        </>

        <View style={styles.rightIcon}>
          <HelpText label="Credit" style={styles.rightText} />
          <LeftArrowIcon />
        </View>
      </View>

      <View style={styles.midView}>
        <View style={styles.rowWrapper}>
          {isSwappedView ? (
            <TextInput
              value={partTerm}
              style={styles.input}
              placeholder="partTerm"
              onChangeText={setPartTerm}
            />
          ) : (
            <TextInput
              value={holdTerm}
              style={styles.input}
              placeholder="holdTerm"
              onChangeText={setHoldTerm}
            />
          )}

          <HelpText helpText="help" label="Limit" style={styles.midText} />

          {isSwappedView ? (
            <TextInput
              value={holdTerm}
              style={styles.input}
              placeholder="holdTerm"
              onChangeText={setHoldTerm}
            />
          ) : (
            <TextInput
              value={partTerm}
              style={styles.input}
              placeholder="partTerm"
              onChangeText={setPartTerm}
            />
          )}
        </View>
      </View>

      <View style={styles.rowWrapper}>
        <View style={styles.leftIcon}>
          <RightArrowIcon />
          <HelpText label="Credit" style={styles.leftText} />
        </View>

        <>
          {isSwappedView ? (
            <View style={styles.bottomCenterWrapper}>
              <View style={styles.circle}>
                <Avatar style={styles.circle} avatar={avatar} />
              </View>
              <HelpText
                helpText="help"
                label="Foil"
                style={styles.headerText}
              />
            </View>
          ) : (
            <View style={styles.bottomCenterWrapper}>
              <View style={styles.circle}>
                <Avatar style={styles.circle} avatar={avatar} />
              </View>

              <HelpText
                helpText="help"
                label="Stock"
                style={styles.headerText}
              />
            </View>
          )}
        </>

        <View style={styles.rightIcon}>
          <UpArrowIcon />
          <HelpText label="Risk" style={styles.rightText} />
        </View>
      </View>

      <View style={styles.absoluteView}>
        <TouchableOpacity onPress={()=>setIsSwappedView(!isSwappedView)}>
        <SwapIcon />
        </TouchableOpacity>
      </View>
    </View>
  );
};

const styles = StyleSheet.create({
  main: {
    flex:1,
    margin: 20,
    paddingTop:20,
    marginHorizontal: 40,
    alignItems: "center",
  },
  circle: {
    height: 100,
    width: 100,
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
    marginTop: 50,
    alignItems: "center",
    justifyContent: "center",
  },
  topCenterWrapper: {
    height: 100,
    marginBottom: 50,
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
    fontSize:12,
    marginRight: 50,
    fontWeight: "500",
  },
  rightText: {
    fontSize:12,
    marginLeft: 50,
    fontWeight: "500",
  },
  absoluteView: {
    top: 0,
    right: 20,
    position: "absolute",
  },
});

export default TallyReviewView;
