import React, { useEffect } from 'react';
import {
  View,
  StyleSheet,
  TextInput,
} from 'react-native';
import { Picker } from '@react-native-picker/picker';

import { colors } from '../../config/constants';
import useMessageText from '../../hooks/useMessageText';

import CustomText from '../../components/CustomText';
import CommonTallyView from '../Tally/CommonTallyView';
import HelpText from '../../components/HelpText';
import { useHoldTermsText } from '../../hooks/useLanguage';

const TallyEditView = (props) => {
  const tally = props.tally;
  const tallyType = props.tallyType;
  const contract = props.contract;
  const holdTerms = props.holdTerms;
  const partTerms = props.partTerms;
  const comment = props.comment;
  const setComment = props.setComment;
  const onHoldTermsChange = props.onHoldTermsChange;
  const onPartTermsChange = props.onPartTermsChange;
  const setTallyType = props.setTallyType;
  const setContract = props.setContract;

  const { messageText } = useMessageText();
  const talliesText = messageText?.tallies;
  const holdTermsText = messageText?.hold_terms_lang;

  useEffect(() => {
    console.log("LANGUAGE ==> ", holdTermsText);
  }, [holdTermsText, messageText])
  return (
    <View>
      <CommonTallyView tally={tally} />

      <View style={styles.detailControl}>
        <HelpText
          label={talliesText?.tally_type?.title ?? ''}
          helpText={talliesText?.tally_type?.help}
          style={styles.headerText}
        />

        <Picker
          mode="dropdown"
          selectedValue={tallyType}
          style={styles.input}
          onValueChange={(item) => {
            setTallyType(item)
          }}
        >
          <Picker.Item label="Stock" value="stock" />
          <Picker.Item label="Foil" value="foil" />
        </Picker>
      </View>

      <View style={styles.detailControl}>
        <HelpText
          label={talliesText?.contract?.title ?? ''}
          helpText={talliesText?.contract?.help}
          style={styles.headerText}
        />

        <Picker
          mode="dropdown"
          style={styles.input}
          selectedValue={contract}
          onValueChange={(item) => {
            setContract(item)
          }}
        >
          <Picker.Item label="Tally Contract" value="Tally_Contract" />
        </Picker>
      </View>

      <View style={styles.detailControl}>
        <HelpText
          label={talliesText?.hold_terms?.title ?? ''}
          helpText={talliesText?.hold_terms?.help}
          style={styles.headerText}
        />

        <View style={{ marginVertical: 10 }}>
          {/* <CustomText as="h5">
            Limit
          </CustomText> */}
          <HelpText
            label={holdTermsText?.[1]?.title ?? ''}
            helpText={holdTermsText?.[1]?.help}
            style={styles.h5}
          />

          <TextInput
            keyboardType='numeric'
            style={styles.input}
            value={holdTerms?.limit}
            onChangeText={onHoldTermsChange('limit')}
          />
        </View>

        <View>
          {/* <CustomText as="h5">
            Call
          </CustomText> */}
          <HelpText
            label={holdTermsText?.[0]?.title ?? ''}
            helpText={holdTermsText?.[0]?.help}
            style={styles.h5}
          />

          <TextInput
            style={styles.input}
            keyboardType='numeric'
            value={holdTerms?.call}
            onChangeText={onHoldTermsChange('call')}
          />
        </View>
      </View>

      <View style={styles.detailControl}>
        <HelpText
          label={talliesText?.part_terms?.title ?? ''}
          helpText={talliesText?.part_terms?.help}
          style={styles.headerText}
        />

        <View style={{ marginVertical: 10 }}>
         {/*  <CustomText as="h5">
            Limit
          </CustomText> */}
          <HelpText
            label={holdTermsText?.[1]?.title ?? ''}
            helpText={holdTermsText?.[1]?.help}
            style={styles.h5}
          />

          <TextInput
            style={styles.input}
            keyboardType='numeric'
            value={partTerms?.limit}
            onChangeText={onPartTermsChange('limit')}
          />
        </View>

        <View>
          {/* <CustomText as="h5">
            Call
          </CustomText> */}
          <HelpText
            label={holdTermsText?.[0]?.title ?? ''}
            helpText={holdTermsText?.[0]?.help}
            style={styles.h5}
          />

          <TextInput
            style={styles.input}
            keyboardType='numeric'
            value={partTerms?.call}
            onChangeText={onPartTermsChange('call')}
          />
        </View>
      </View>

      <View style={styles.detailControl}>
        <HelpText
          label={talliesText?.comment?.title ?? ''}
          helpText={talliesText?.comment?.help}
          style={styles.headerText}
        />

        <TextInput
          multiline
          numberOfLines={4}
          value={comment}
          style={[styles.input, styles.comment]}
          onChangeText={setComment}
        />
      </View>
    </View>
  )
}

const styles = StyleSheet.create({
  detailControl: {
    marginVertical: 10
  },
  input: {
    padding: 10,
    backgroundColor: colors.gray100,
  },
  comment: {
    textAlignVertical: 'top',
  },
  actions: {
    flexDirection: 'row',
  },
  headerText: {
    color: colors.black,
    fontSize: 14,
  },
  h5: {
    fontSize: 12,
    lineHeight: 16,
    fontWeight: 'bold',
  },
})

export default TallyEditView;
