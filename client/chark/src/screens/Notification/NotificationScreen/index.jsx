import React from "react";
import { View, Text, StyleSheet, FlatList } from "react-native";
import NavigationItem from "../NotificationItem";
import { colors } from "../../../config/constants";

const NotificationScreen = () => {

    //DUMMY DATA - Needs discussion
  const notificationItem = [
    {
      id: 0,
      name: "Harold Law",
      status: "Tally Request",
      time: "45 min",
      amount: "32 USD",
      totalAmount: "12.01",
    },
    {
      id: 1,
      name: "Brad Collins",
      status: "Paid You",
      time: "2 months",
      amount: "32 USD",
      totalAmount: "12.01",
    },
    {
      id: 2,
      name: "Jason Bourne",
      status: "You Paid",
      time: "4 months",
      amount: "32 USD",
      totalAmount: "12.01",
    },
  ];

  return (
    <View style={styles.main}>
      <FlatList
        data={notificationItem}
        keyExtractor={(item) => item.id}
        renderItem={({ item,index }) => {
          return (
            <View
              style={[
                styles.item,
                  index === notificationItem?.length - 1 ? styles.itemLast : null,
              ]}
            >
              <NavigationItem notification={item} />
            </View>
          );
        }}
      />
    </View>
  );
};

const styles = StyleSheet.create({
  main: {
    flex:1,
    paddingHorizontal: 20,
    paddingVertical: 15,
  },
  item: {
    paddingVertical: 18,
    borderBottomWidth: 1,
    paddingHorizontal: 12,
    borderBottomColor: colors.lightgray,
  },
  itemLast: {
    borderBottomWidth: 0,
  },
});

export default NotificationScreen;
