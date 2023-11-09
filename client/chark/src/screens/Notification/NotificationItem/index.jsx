import React, { useEffect, useState } from "react";
import { View, Text, StyleSheet } from "react-native";

import Avatar from "../../../components/Avatar";
import Button from "../../../components/Button";
import { colors } from "../../../config/constants";
import { ChitIcon } from "../../../components/SvgAssets/SvgAssets";

const NavigationItem = (props) => {
// Dummy data used for UI Purpose - needs discussion

  const notification = props.notification;

  const TallyView = () => {
    return (
      <View style={styles.price}>
        <Text style={[styles.description, { marginBottom: 8 }]}>
          {notification.time}
        </Text>

        <View style={styles.myChips}>
          {notification.status === "You Paid" ? (
            <Text style={styles.myChipsNetNeg}>-</Text>
          ) : (
            <Text style={styles.myChipsNet}>+</Text>
          )}
          <ChitIcon
            color={
              notification.status === "You Paid" ? colors.red : colors.green
            }
            height={18}
            width={12}
          />
          <Text
            style={
              notification.status === "You Paid"
                ? styles.myChipsNetNeg
                : styles.myChipsNet
            }
          >
            {notification.totalAmount}
          </Text>
        </View>

        <Text style={styles.description}>{notification.amount}</Text>
      </View>
    );
  };


  const InvitationView = () => {
    return (
      <View style={styles.price}>
        <Text style={[styles.description, { marginBottom: 5 }]}>
          {notification.time}
        </Text>

        <View style={styles.buttonView}>
          <Button
            textStyle={styles.text}
            textColor="blue"
            title="View Cert"
            onPress={()=>{}}
            style={styles.secondaryButton}
          />

          <Button
            textStyle={styles.text}
            title="Accept"
            onPress={()=>{}}
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
        <Text style={styles.name}>{notification.name}</Text>
        <Text style={[styles.description, { marginTop: 4 }]}>
          {notification.status}
        </Text>
      </View>

      {notification.status === 'Tally Request' ?
      <InvitationView/>
    :    <TallyView />
    }

  
    </View>
  );
};

const myChipsNet = {
  fontSize: 18,
  paddingBottom:3,
  fontWeight: "600",
  color: colors.green,
};

const styles = StyleSheet.create({
  button: {
    height:23,
    marginBottom: 3,
    borderRadius: 40,
    paddingVertical:0,
    borderColor: "blue",
    alignItems: "center",
    backgroundColor: "blue",
    borderColor: "blue",
    borderRadius: 40,
    marginBottom: 3,
    borderRadius: 40,
    paddingVertical:0,
    borderColor: "blue",
    alignItems: "center",
    backgroundColor: "blue",
    justifyContent: "center",
  },
  secondaryButton: {
    height:23,
    marginBottom: 3,
    borderRadius: 40,
    paddingVertical:0,
    borderColor: "blue",
    alignItems: "center",
    backgroundColor: "white",
    borderColor: "blue",
    borderRadius: 40,
    alignItems: "center",
    justifyContent: "center",
    marginBottom: 3,
    borderRadius: 40,
    paddingVertical:0,
    borderColor: "blue",
    alignItems: "center",
    backgroundColor: "white",
    justifyContent: "center",
  },
  container: {
    height:50,
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
  buttonView:{
    marginLeft:10
  },
  text:{
    fontSize:10
  }
});


export default NavigationItem;
