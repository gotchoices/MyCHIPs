import React, { useState, useMemo, useRef, useEffect} from "react";
import PropTypes from 'prop-types';
import { View, Text, TextInput, StyleSheet, TouchableOpacity, ScrollView } from "react-native";

import Button from "../../../components/Button";
import CustomIcon from "../../../components/CustomIcon";

import { colors } from "../../../config/constants";
import { round } from "../../../utils/common";

const CommentContent = (props) => {
  const [comment, setComment] = useState();
  const [selectedItem, setSelectedItem] = useState('foil');
  const [myLimit, setMyLimit] = useState(0);
  const [partnerLimit, setPartnerLimit] = useState(0);

  const holdTermsText = props?.text?.hold_terms;
  const partTermsText = props?.text?.part_terms;

  const textRef= useRef()

  const holdLimitText = useMemo(() => {
    return holdTermsText?.values?.find((term) => term.value === 'limit')
  }, [holdTermsText?.values])

  const partLimitText = useMemo(() => {
    return partTermsText?.values?.find((term) => term.value === 'limit')
  }, [partTermsText?.values])

  const tallyTypeText = useMemo(() => {
    return props.text?.tally_type?.values?.reduce((acc, current) => {
      acc[current.value] = current;
      return acc;
    }, {})
  })

  const generateCommonStyle = (itemType, selected) => ({
    flex: 1,
    alignItems: 'center',
    justifyContent: 'center',
    borderWidth: 1,
    borderEndWidth: itemType === "foil" ? 0 : 1,
    borderColor: selected ? 'blue' : '#D7D7D7',
    backgroundColor: selected ? 'blue' : colors.white,
    borderTopLeftRadius: itemType === "foil" ? 6 : 0,
    borderBottomLeftRadius: itemType === "foil" ? 6 : 0,
    borderTopRightRadius: itemType === "stock" ? 6 : 0,
    borderBottomRightRadius: itemType === "stock" ? 6 : 0,

  });

  const checkValidInput = (textValue) => {
    return textValue && /^[0-9]*(\.[0-9]{0,3})?$/.test(textValue);
  };

  const getValidAmount = (amount) => {
    if (parseFloat(amount) > 0) {
      return amount;
    }

    return 1.000
  };

  const calculateSendingAmount = (value, setLimit) => {
    const amount = getValidAmount(value);

    if (amount && checkValidInput(amount)) {
      return setLimit(amount);
    }

    return setLimit(
     round(amount, 3)
    );
  };

  useEffect(()=>{
    if(textRef){
      textRef.current.focus()
    }
  },[props])

  const holdText = (holdLimitText?.title ?? '') + ` (${holdTermsText?.title ?? ''})`
  const partText = (partLimitText?.title ?? '') + ` (${partTermsText?.title ?? ''})`

  return (
    <View style={styles.bottomSheetContainer}>
      <CustomIcon
        name="close"
        size={16}
        onPress={props.onDismiss}
        style={{ alignSelf: 'flex-end', backgroundColor: 'white', height: 24, width: 24, justifyContent: 'center', alignItems: 'center' }}
      />

      <Text style={styles.bottomSheetTitle}>{props?.text?.newtally?.title ?? ''}</Text>

      <TextInput
        ref={textRef}
        autoFocus
        numberOfLines={1}
        returnKeyType="done"
        keyboardType="numeric"
        style={styles.textInput}
        value={myLimit ? myLimit : ''}
        onChangeText={(text) => calculateSendingAmount(text, setMyLimit)}
        placeholder={holdText}
      />

      <TextInput
        maxLength={9}
        numberOfLines={1}
        returnKeyType="done"
        keyboardType="numeric"
        style={styles.textInput}
        value={partnerLimit ?  partnerLimit : ''}
        onChangeText={(text) => calculateSendingAmount(text, setPartnerLimit)}
        placeholder={partText}
      />

      <View style={styles.selectorParent}>
        <TouchableOpacity
          onPress={() => { setSelectedItem('foil') }}
          style={generateCommonStyle('foil', selectedItem === "foil")}
        >
          <Text style={selectedItem === "foil" ? styles.selectedLabel : styles.unSelectedLabel}>{tallyTypeText?.foil?.title ?? ''}</Text>
        </TouchableOpacity>

        <TouchableOpacity
          onPress={() => { setSelectedItem('stock') }}
          style={generateCommonStyle('stock', selectedItem === "stock")}
        >
          <Text style={selectedItem === "stock" ? styles.selectedLabel : styles.unSelectedLabel}>{tallyTypeText?.stock?.title ?? ''}</Text>
        </TouchableOpacity>
      </View>

      <TextInput
        value={comment}
        onChangeText={setComment}
        placeholder={props.text?.comment?.title ?? ''}
        style={styles.textInput}
        returnKeyType="done"
      />


      <Button
        title={props?.text?.next?.title ?? ''}
        onPress={() => {
          props.onNext({ comment: comment, tally_type: selectedItem, myLimit, partnerLimit });
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
    paddingHorizontal: 24,
    paddingVertical: 24,
    alignItems: 'center',
  },
  bottomSheetTitle: {
    marginBottom: 25,
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
    marginVertical: 14,
    //marginTop: 40,
    height: 40,
  },
  selectorParent: {
    width: "90%",
    height: 60,
    flexDirection: 'row',
    marginVertical: 16,
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
    marginBottom:40,
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
