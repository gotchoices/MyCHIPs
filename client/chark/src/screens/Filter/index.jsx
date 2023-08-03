import React, { useState } from "react";
import { View, StyleSheet, Text, TouchableOpacity } from "react-native";
import { colors } from "../../config/constants";
import { SelectedIcon, SwitchSelectedIcon, SwitchUnselectedIcon, SwithcKeyIcon, UnSelectedIcon } from "../../components/SvgAssets/SvgAssets";

const FilterItem = ({ args, onSelected }) => {

  const onPress = () => {
    onSelected(args)
  }

  return <View style={styles.row}>
    <Text style={styles.title}>{args.title}</Text>
    <TouchableOpacity style={{ justifyContent: 'center' }} onPress={onPress}>
      {args.selected ? <SelectedIcon /> : <UnSelectedIcon />}
    </TouchableOpacity>
  </View >
}

const FilterScreen = () => {
  const initialFilter = {
    offer: { title: "Offers", selected: false, status: 'offer' },
    draft: { title: "Drafts", selected: false, status: 'draft' },
    void: { title: "Voids", selected: false, status: 'void' },
  }

  const [filter, setFilter] = useState(initialFilter);

  const onSelected = (args) => {
    const updatedData = {
      ...filter,
      [args.status]: { ...args, selected: !args.selected }
    }
    setFilter(updatedData);
  }

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


const styles = StyleSheet.create({
  container: {
    flex: 1,
    backgroundColor: colors.white,
  },
  display: {
    fontWeight: '400',
    fontSize: 16,
    padding: 16,
  },
  title: {
    fontSize: 14,
    color: colors.black,
    fontWeight: '500'
  },
  row: {
    flexDirection: 'row', justifyContent: 'space-between', paddingHorizontal: 24,
  },
  divider: {
    height: 1, backgroundColor: '#ADADAD', width: '100%', marginVertical: 12
  }
})

export default FilterScreen;