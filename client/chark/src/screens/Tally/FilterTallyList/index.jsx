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
import useMessageText from '../../../hooks/useMessageText';

import {
  SelectedIcon,
  UnSelectedIcon,
} from "../../../components/SvgAssets/SvgAssets";
import { setFilterTally } from "../../../redux/profileSlice";

const FilterItem = ({ args, onSelected, title }) => {
  const onPress = () => {
    onSelected(args);
  };

  return (
    <View style={styles.row}>
      <Text style={styles.title}>{title}</Text>
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
  const { messageText } = useMessageText();
  const talliesMeMessageText = messageText?.tallies_v_me?.msg

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
        selected: true,
        status: "recent",
      },
      ascending: {
        selected: false,
        status: "ascending",
      },
      descending: {
        selected: false,
        status: "descending",
      },
      absolute: {
        selected: false,
        status: "absolute",
      },
      alphabetical: {
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
          <FilterItem 
            args={filter.recent} 
            onSelected={onSelected} 
            title={talliesMeMessageText?.['sort.ddate']?.title ?? ''}
          />
          <View style={styles.divider} />

          <FilterItem
            args={filter.ascending}
            onSelected={onSelected}
            title={talliesMeMessageText?.['sort.dbal']?.title ?? ''}
          />
          <View style={styles.divider} />

          <FilterItem
            args={filter.descending}
            onSelected={onSelected}
            title={talliesMeMessageText?.['sort.abal']?.title ?? ''}
          />
          <View style={styles.divider} />

          <FilterItem
            args={filter.absolute}
            onSelected={onSelected}
            title={talliesMeMessageText?.['sort.mbal']?.title ?? ''}
          />
          <View style={styles.divider} />

          <FilterItem
            args={filter.alphabetical}
            onSelected={onSelected}
            title={talliesMeMessageText?.['sort.dname']?.title ?? ''}
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
    padding: 16,
    fontSize: 16,
    fontWeight: "400",
    fontFamily: "inter",
  },
  title: {
    fontSize: 14,
    fontWeight: "500",
    color: colors.black,
    fontFamily: "inter",
  },
  row: {
    flexDirection: "row",
    paddingHorizontal: 24,
    justifyContent: "space-between",
  },
  divider: {
    height: 1,
    width: "100%",
    marginVertical: 12,
    backgroundColor: "#ADADAD",
  },
  reset: {
    fontSize: 14,
    color: "#636363",
    fontWeight: "500",
    fontFamily: "inter",
  },
});

export default FilterTallyScreen;
