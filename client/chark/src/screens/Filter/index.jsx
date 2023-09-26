import React, { useEffect } from "react";
import { View, StyleSheet, Text, TouchableOpacity, ActivityIndicator } from "react-native";
import AsyncStorage from "@react-native-async-storage/async-storage";
import { useSelector, useDispatch } from 'react-redux';

import { colors } from "../../config/constants";
import { setFilter } from "../../redux/profileSlice";
import { SelectedIcon, UnSelectedIcon } from "../../components/SvgAssets/SvgAssets";

const FilterItem = ({ args, onSelected }) => {
  const onPress = () => {
    onSelected(args)
  }

  return <View style={styles.row}>
    <Text style={styles.title}>{args?.title}</Text>
    <TouchableOpacity style={{ justifyContent: 'center' }} onPress={onPress}>
      {args?.selected ? <SelectedIcon /> : <UnSelectedIcon />}
    </TouchableOpacity>
  </View >
}

const FilterScreen = (props) => {
  const { filter } = useSelector(state => state.profile);
  const navigation = props.navigation;
  const dispatch = useDispatch();

  useEffect(() => {
    const addButtonToTopBar = () => {
      navigation.setOptions({
        headerRight: () => (
          <TouchableOpacity onPress={onClear} style={{ marginRight: 16 }}>
            <Text style={styles.reset}>Reset</Text>
          </TouchableOpacity>
        ),
      });
    };
    addButtonToTopBar();

    return () => {
      navigation.setOptions({
        headerRight: undefined,
      });
    };
  }, [navigation]);


  const onClear = () => {
    const resetFilter = {
      offer: { title: "Offers", selected: false, status: 'offer' },
      draft: { title: "Drafts", selected: false, status: 'draft' },
      void: { title: "Voids", selected: false, status: 'void' },
    }
    AsyncStorage.setItem("filterData", JSON.stringify(resetFilter)).then(() => {
      dispatch(setFilter(resetFilter))
    })
  }

  const onSelected = (args) => {
    const updatedData = {
      ...filter,
      [args.status]: { ...args, selected: !args?.selected }
    }
    AsyncStorage.setItem("filterData", JSON.stringify(updatedData)).then(() => {
      dispatch(setFilter(updatedData));
    })
  }

  if (filter) {
    return <View style={styles.container}>
      <Text style={styles.display}>Display</Text>

      <View style={styles.divider} />

      <FilterItem args={filter.offer} onSelected={onSelected} />
      <View style={styles.divider} />

      <FilterItem args={filter.draft} onSelected={onSelected} />
      <View style={styles.divider} />

      <FilterItem args={filter.void} onSelected={onSelected} />
      <View style={styles.divider} />
    </View>
  }

  return <View style={{ flex: 1, justifyContent: 'center', alignItems: 'center' }}>
    <ActivityIndicator />
  </View>
}


const styles = StyleSheet.create({
  container: {
    flex: 1,
    backgroundColor: colors.white,
  },
  display: {
    fontWeight: '400',
    fontSize: 16,
    padding: 16,
    fontFamily: 'inter'
  },
  title: {
    fontSize: 14,
    color: colors.black,
    fontWeight: '500',
    fontFamily: 'inter'
  },
  row: {
    flexDirection: 'row',
    justifyContent: 'space-between',
    paddingHorizontal: 24,
  },
  divider: {
    height: 1,
    backgroundColor: '#ADADAD',
    width: '100%',
    marginVertical: 12
  },
  reset: {
    fontSize: 14,
    fontWeight: '500',
    fontFamily: 'inter',
    color: '#636363',
  }
})

export default FilterScreen;
