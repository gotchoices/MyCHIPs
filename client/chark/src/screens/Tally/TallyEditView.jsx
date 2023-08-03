import React, { useState, useEffect } from 'react';
import {
  View,
  StyleSheet,
  TextInput,
  TouchableWithoutFeedback,
  Text,
} from 'react-native';
import { Picker } from '@react-native-picker/picker';

import { colors } from '../../config/constants';
import useMessageText from '../../hooks/useMessageText';
import useSocket from '../../hooks/useSocket';
import { fetchContracts } from '../../services/tally';

import CustomText from '../../components/CustomText';
import CommonTallyView from '../Tally/CommonTallyView';
import HelpText from '../../components/HelpText';
import CustomButton from '../../components/Button';

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
  const [tallyContracts, setTallyContracts] = useState([]);

  const { wm } = useSocket();
  const { messageText } = useMessageText();
  const talliesText = messageText?.tallies;

  useEffect(() => {
    fetchContracts(wm, {
      fields: ['top', 'name', 'title', 'language', 'host', 'rid', 'clean'],
      where: { top: true },
    }).then((data) => {
      setTallyContracts((prev) => ([
        ...prev,
        ...data,
      ]));
    })
  }, [])

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
        {
          tallyContracts.map((tallyContract) => (
            <Picker.Item key={tallyContract.name} label={tallyContract.title} value={tallyContract.name} />
          ))
        }
        </Picker>

        <CustomButton
          title="Show PDF"
          onPress={props.onViewContract}
          textColor={colors.blue}
          style={styles.showPDF}
        />
      </View>

      <View style={styles.detailControl}>
        <HelpText
          label={talliesText?.hold_terms?.title ?? ''}
          helpText={talliesText?.hold_terms?.help}
          style={styles.headerText}
        />

        <View style={{ marginVertical: 10 }}>
          <CustomText as="h5">
            Limit
          </CustomText>

          <TextInput
            keyboardType='numeric'
            style={styles.input}
            value={holdTerms?.limit}
            onChangeText={onHoldTermsChange('limit')}
          />
        </View>

        <View>
          <CustomText as="h5">
            Call
          </CustomText>

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
          <CustomText as="h5">
            Limit
          </CustomText>

          <TextInput
            style={styles.input}
            keyboardType='numeric'
            value={partTerms?.limit}
            onChangeText={onPartTermsChange('limit')}
          />
        </View>

        <View>
          <CustomText as="h5">
            Call
          </CustomText>

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
  showPDF: {
    marginVertical: 8,
    color: colors.blue,
    backgroundColor: colors.white,
  }
})

export default TallyEditView;
