import React, { useState } from "react";
import { View, Text, TextInput, StyleSheet, TouchableOpacity, ScrollView } from "react-native";
import Button from "../../../components/Button";
import CustomIcon from "../../../components/CustomIcon";
import PropTypes from 'prop-types';
import { colors } from "../../../config/constants";

const CommentContent = (props) => {
  const [comment, setComment] = useState();
  const [selectedItem, setSelectedItem] = useState(undefined);

  const generateCommonStyle = (itemType, selected) => ({
    flex: 1,
    alignItems: 'center',
    justifyContent: 'center',
    borderWidth: 1,
    borderEndWidth: itemType === "foil" ? 0 : 1,
    borderColor: selected ? 'blue' : '#D7D7D7',
    backgroundColor: selected ? 'blue' : '#F5F5F5',
    borderTopLeftRadius: itemType === "foil" ? 6 : 0,
    borderBottomLeftRadius: itemType === "foil" ? 6 : 0,
    borderTopRightRadius: itemType === "stock" ? 6 : 0,
    borderBottomRightRadius: itemType === "stock" ? 6 : 0,

  });

  return (<View style={styles.bottomSheetContainer}>
    <CustomIcon
      name="close"
      size={16}
      onPress={props.onDismiss}
      style={{ alignSelf: 'flex-end', backgroundColor: 'white', height: 24, width: 24, justifyContent: 'center', alignItems: 'center' }}
    />
    <Text style={styles.bottomSheetTitle}>New Tally</Text>
    <TextInput
      value={comment}
      onChangeText={setComment}
      placeholder='Comments'
      style={styles.textInput}
      returnKeyType="done"
    />

    <View style={styles.selectorParent}>
      <TouchableOpacity
        onPress={() => { setSelectedItem('foil') }}
        style={generateCommonStyle('foil', selectedItem === "foil")}
      >
        <Text style={selectedItem === "foil" ? styles.selectedLabel : styles.unSelectedLabel}>Foil</Text>
      </TouchableOpacity>

      <TouchableOpacity
        onPress={() => { setSelectedItem('stock') }}
        style={generateCommonStyle('stock', selectedItem === "stock")}
      >
        <Text style={selectedItem === "stock" ? styles.selectedLabel : styles.unSelectedLabel}>Stock</Text>
      </TouchableOpacity>
    </View>

    <Button
      title='Next'
      onPress={() => {
        props.onNext({ comment: comment, tally_type: selectedItem });
      }}
      style={styles.button}
    />
  </View>);
}


CommentContent.propTypes = {
  onNext: PropTypes.func.isRequired,
  onDismiss: PropTypes.func.isRequired,
}

const styles = StyleSheet.create({
  bottomSheetContainer: {
    height: 600,
    paddingHorizontal: 16,
    paddingVertical: 24,
    alignItems: 'center',
  },
  bottomSheetTitle: {
    fontSize: 25,
    fontWeight: '400',
    fontFamily: 'inter',
    color: colors.black,
  },
  textInput: {
    borderWidth: 1,
    borderColor: '#BBBBBB',
    paddingHorizontal: 12,
    paddingVertical: 0,
    width: '100%',
    borderRadius: 6,
    marginTop: 40,
    height: 40,
  },
  selectorParent: {
    width: "80%",
    height: 60,
    flexDirection: 'row',
    marginTop: 35,
    borderRadius: 6,
  },
  selectedLabel: {
    fontSize: 18,
    color: 'white',
  },
  unSelectedLabel: {
    fontSize: 18,
    color: '#B6B6B6'
  },
  button: {
    backgroundColor: 'blue',
    borderColor: 'blue',
    width: '100%',
    borderRadius: 40,
    height: 45,
    alignItems: 'center',
    justifyContent: 'center',
    bottom: 0,
    position: 'absolute',
    marginVertical: 24,
  }
});

const selectedCommonStyle = {
  flex: 1,
  alignItems: 'center',
  justifyContent: 'center',
  borderWidth: 1,
  borderColor: 'blue',
  backgroundColor: 'blue',
}

const unSelectedCommonStyle = {
  flex: 1,
  alignItems: 'center',
  justifyContent: 'center',
  borderWidth: 1,
  borderColor: '#D7D7D7',
  backgroundColor: '#F5F5F5',
}

export default CommentContent;