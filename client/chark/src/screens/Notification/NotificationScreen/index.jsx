import React, { useEffect, useState } from "react";
import { View, StyleSheet, FlatList, ActivityIndicator } from "react-native";

import { colors } from "../../../config/constants";
import NotificationTallyRequest from "../NotificationTallyRequest";
import { fetchTallies } from "../../../services/tally";
import useSocket from "../../../hooks/useSocket";

const NotificationScreen = (props) => {
  const { wm } = useSocket();

  const [loading, setLoading] = useState(true);

  const [actionTallies, setActionTallies] = useState();

  useEffect(() => {
    fetchTally();
  }, []);

  const fetchTally = () => {
    fetchTallies(wm, {
      fields: [
        'tally_ent',
        'tally_seq',
        'contract',
        'comment',
        'tally_uuid',
        'hold_terms',
        'part_terms',
        'tally_type',
        'status',
        'part_cid',
        'part_cert',
        'hold_cert',
        'json',
        'state',
      ],
      where: ["action true"],
    })
      .then((data) => {
        setActionTallies(data);
      })
      .catch((e) => {
        console.log("ERROR===>", e);
      })
      .finally(() => {
        setLoading(false);
      });
  };

  if (loading) {
    return (
      <View style={{ flex: 1, justifyContent: "center", alignItems: "center" }}>
        <ActivityIndicator size={"large"} />
      </View>
    );
  }

  return (
    <View style={styles.main}>
      <FlatList
        data={actionTallies}
        keyExtractor={(item) => item.id}
        renderItem={({ item, index }) => {
          return (
            <View
              style={[
                styles.item,
                index === actionTallies?.length - 1 ? styles.itemLast : null,
              ]}
            >
              <NotificationTallyRequest tally={item}  navigation={props.navigation} />
            </View>
          );
        }}
      />
    </View>
  );
};

const styles = StyleSheet.create({
  main: {
    flex: 1,

    paddingTop: 5,
    paddingBottom: 15,
    paddingHorizontal: 20,
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
