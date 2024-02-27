import React, { useEffect, useMemo } from "react";
import { View, StyleSheet, Text, TouchableOpacity, ActivityIndicator } from "react-native";
import AsyncStorage from "@react-native-async-storage/async-storage";
import { useSelector, useDispatch } from 'react-redux';

import { colors } from "../../config/constants";
import { setFilter } from "../../redux/profileSlice";
import useSocket from "../../hooks/useSocket";
import { useTalliesMeText } from "../../hooks/useLanguage";
import { SelectedIcon, UnSelectedIcon } from "../../components/SvgAssets/SvgAssets";

const FilterItem = ({ args, onSelected, title }) => {
  const onPress = () => {
    onSelected(args)
  }

  return <View style={styles.row}>
    <Text style={styles.title}>{title}</Text>
    <TouchableOpacity style={{ justifyContent: 'center' }} onPress={onPress}>
      {args?.selected ? <SelectedIcon /> : <UnSelectedIcon />}
    </TouchableOpacity>
  </View >
}

const FilterScreen = (props) => {
  const { filter } = useSelector(state => state.profile);
  const navigation = props.navigation;
  const dispatch = useDispatch();
  const { wm } = useSocket();
  const talliesText = useTalliesMeText(wm);
  const talliesMeText = talliesText?.col;

  const hasFilterChanged = useMemo(() => {
    const isOfferSelected = filter?.offer?.selected === true;
    const isDraftSelected = filter?.draft?.selected === true;
    const isVoidSelected = filter?.void?.selected === true;

    if(!isOfferSelected || !isDraftSelected || !isVoidSelected) {
      return true;
    }

    return false;
  }, [filter])

  useEffect(() => {
    const addButtonToTopBar = () => {
      navigation.setOptions({
        headerRight: () => (
          <TouchableOpacity onPress={onReset} style={{ marginRight: 16 }}>
            <Text style={styles.reset}>Reset</Text>
          </TouchableOpacity>
        ),
      });
    };

    if(hasFilterChanged) {
      addButtonToTopBar();
    }

    return () => {
      navigation.setOptions({
        headerRight: undefined,
      });
    };
  }, [navigation, hasFilterChanged]);

  const statusText = useMemo(() => {
    return talliesMeText?.status?.values?.reduce((acc, current) => {
      acc[current?.value] = current;
      return acc;
    }, {})
  }, [talliesMeText?.status?.values])


  const onReset = () => {
    const resetFilter = {
      offer: { selected: true, status: 'offer' },
      draft: { selected: true, status: 'draft' },
      void: { selected: true, status: 'void' },
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
      <View style={styles.divider} />

      <FilterItem args={filter.offer} onSelected={onSelected} title={statusText?.offer?.title ?? 'offer_text'} />
      <View style={styles.divider} />

      <FilterItem args={filter.draft} onSelected={onSelected} title={statusText?.draft?.title ?? ''} />
      <View style={styles.divider} />

      <FilterItem args={filter.void} onSelected={onSelected} title={statusText?.void?.title ?? ''} />
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
