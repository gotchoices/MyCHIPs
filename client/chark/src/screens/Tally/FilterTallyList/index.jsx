import React, { useEffect, useMemo } from "react";
import {
  View,
  Text,
  StyleSheet,
  TouchableOpacity,
  ActivityIndicator,
} from "react-native";

import { colors } from "../../../config/constants";
import { useSelector, useDispatch } from "react-redux";
import AsyncStorage from "@react-native-async-storage/async-storage";

import {
  SelectedIcon,
  UnSelectedIcon,
} from "../../../components/SvgAssets/SvgAssets";
import { setFilterTally } from "../../../redux/profileSlice";

const FilterItem = ({ args, onSelected }) => {
  const onPress = () => {
    onSelected(args);
  };

  return (
    <View style={styles.row}>
      <Text style={styles.title}>{args?.title}</Text>
      <TouchableOpacity
        style={{ justifyContent: "center" }}
        onPress={onPress}
      >
        {args?.selected ? <SelectedIcon /> : <UnSelectedIcon />}
      </TouchableOpacity>
    </View>
  );
};

const FilterTallyScreen = (props) => {
  const filter = useSelector((state) => state.profile.filterTally);

  const dispatch = useDispatch();
  const navigation = props.navigation;

  const hasFilterChanged = useMemo(() => {
    const isRecentSelected = filter.recent.selected === true;
    const isAscendingSelected = filter.ascending.selected === true;
    const isDescendingSelected = filter.descending.selected === true;
    const isAbsoluteSelected = filter.absolute.selected === true;
    const isAlphabeticalSelected =
      filter.alphabetical.selected === true;

    if (
      !isRecentSelected ||
      !isAscendingSelected ||
      !isDescendingSelected ||
      !isAbsoluteSelected ||
      !isAlphabeticalSelected
    ) {
      return true;
    }

    return false;
  }, [filter]);

  useEffect(() => {
    const addButtonToTopBar = () => {
      navigation.setOptions({
        headerRight: () => (
          <TouchableOpacity
            onPress={onReset}
            style={{ marginRight: 16 }}
          >
            <Text style={styles.reset}>Reset</Text>
          </TouchableOpacity>
        ),
      });
    };

    if (hasFilterChanged) {
      addButtonToTopBar();
    }

    return () => {
      navigation.setOptions({
        headerRight: undefined,
      });
    };
  }, [navigation, hasFilterChanged]);

  const onReset = () => {
    const resetFilter = {
      recent: {
        title: "Most Recent activity",
        selected: true,
        status: "recent",
      },
      ascending: {
        title: "Positive to Negative (assets to liabilities)",
        selected: false,
        status: "ascending",
      },
      descending: {
        title: "Negative to Positive (liabilities to assets)",
        selected: false,
        status: "descending",
      },
      absolute: {
        title: "Absolute value (highest to lowest)",
        selected: false,
        status: "absolute",
      },
      alphabetical: {
        title: "Alphabetical",
        selected: false,
        status: "alphabetical",
      },
    };

    AsyncStorage.setItem(
      "filterTallyList",
      JSON.stringify(resetFilter)
    ).then(() => {
      dispatch(setFilterTally(resetFilter));
    });
  };

  const onSelected = (args) => {
    const updatedData = { ...filter };

    Object.keys(updatedData).forEach((key) => {
      updatedData[key] = {
        ...updatedData[key],
        selected: key === args.status,
      };
    });

    AsyncStorage.setItem(
      "filterTallyList",
      JSON.stringify(updatedData)
    ).then(() => {
      dispatch(setFilterTally(updatedData));
    });
  };

  return (
    <View style={{ flex: 1 }}>
      {filter ? (
        <View style={styles.container}>
          <FilterItem args={filter.recent} onSelected={onSelected} />
          <View style={styles.divider} />

          <FilterItem
            args={filter.ascending}
            onSelected={onSelected}
          />
          <View style={styles.divider} />

          <FilterItem
            args={filter.descending}
            onSelected={onSelected}
          />
          <View style={styles.divider} />

          <FilterItem
            args={filter.absolute}
            onSelected={onSelected}
          />
          <View style={styles.divider} />

          <FilterItem
            args={filter.alphabetical}
            onSelected={onSelected}
          />
          <View style={styles.divider} />
        </View>
      ) : (
        <View
          style={{
            flex: 1,
            alignItems: "center",
            justifyContent: "center",
          }}
        >
          <ActivityIndicator />
        </View>
      )}
    </View>
  );
};

const styles = StyleSheet.create({
  container: {
    flex: 1,
    paddingTop: 20,
    backgroundColor: colors.white,
  },
  display: {
    fontWeight: "400",
    fontSize: 16,
    padding: 16,
    fontFamily: "inter",
  },
  title: {
    fontSize: 14,
    color: colors.black,
    fontWeight: "500",
    fontFamily: "inter",
  },
  row: {
    flexDirection: "row",
    justifyContent: "space-between",
    paddingHorizontal: 24,
  },
  divider: {
    height: 1,
    backgroundColor: "#ADADAD",
    width: "100%",
    marginVertical: 12,
  },
  reset: {
    fontSize: 14,
    fontWeight: "500",
    fontFamily: "inter",
    color: "#636363",
  },
});

export default FilterTallyScreen;
