import React, { useState, useEffect } from 'react';
import {
  View,
  StyleSheet,
  TextInput,
} from 'react-native';
import { Picker } from '@react-native-picker/picker';
import { colors } from '../../config/constants';
import useMessageText from '../../hooks/useMessageText';

import CommonTallyView from '../Tally/CommonTallyView';
import HelpText from '../../components/HelpText';
import CustomButton from '../../components/Button';
import TallyReviewView from '../TallyReview/TallyReviewView';

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
  const tallyContracts = props.tallyContracts ?? [];

  const { messageText } = useMessageText();
  const talliesText = messageText?.tallies;
  const holdTermsText = messageText?.terms_lang?.hold_terms?.values;
  const partTermsText = messageText?.terms_lang?.part_terms?.values;
  const hasPartCert = !!tally?.part_cert;
  const hasHoldCert = !!tally?.hold_cert;
  const isCertUpdateable = tally?.status === 'draft';

  return (
    <View>
      <TallyReviewView tally={tally} />

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
          <Picker.Item label="Select contract" />
          {
            tallyContracts.map((tallyContract) => (
              <Picker.Item key={tallyContract.name} label={tallyContract.title} value={tallyContract.rid} />
            ))
          }
        </Picker>

        <CustomButton
          title="Show PDF"
          onPress={props.onViewContract}
          textColor={colors.blue}
          style={styles.showPDF}
        />

        {
          isCertUpdateable ? <CustomButton
            title="Update Certificate"
            onPress={props.onUpdateContract}
            textColor={colors.blue}
            style={styles.showPDF}
          /> : <></>
        }

        {
          hasPartCert ? <CustomButton
            title="View Partner Certificate"
            onPress={() => props.onViewCertificate({ title: 'Partner Certificate', data: tally?.part_cert })}
            textColor={colors.blue}
            style={styles.showPDF}
          /> : <></>
        }

        {
          hasHoldCert ? <CustomButton
            title="View Holder Certificate"
            onPress={() => props.onViewCertificate({ title: 'Holder Certificate', data: tally?.hold_cert })}
            textColor={colors.blue}
            style={styles.showPDF}
          /> : <></>
        }
      </View>

      <View style={styles.detailControl}>
        <HelpText
          label={talliesText?.hold_terms?.title ?? ''}
          helpText={talliesText?.hold_terms?.help}
          style={styles.headerText}
        />

        {
          holdTermsText?.map((holdTerm, index) => {
            return <View key={`${holdTerm?.value}${index}`} style={{ marginVertical: 10 }}>
              <HelpText
                label={holdTerm?.title ?? ''}
                helpText={holdTerm?.help}
                style={styles.h5}
              />

              <TextInput
                keyboardType='numeric'
                style={styles.input}
                value={holdTerms?.[holdTerm?.value]}
                // value={holdTerms?.limit}
                onChangeText={onHoldTermsChange(holdTerm?.value)}
              />
            </View>
          })
        }

        {/*  <View style={{ marginVertical: 10 }}>
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
        </View> */}
      </View>

      <View style={styles.detailControl}>
        <HelpText
          label={talliesText?.part_terms?.title ?? ''}
          helpText={talliesText?.part_terms?.help}
          style={styles.headerText}
        />
        {
          partTermsText?.map((partTerm, index) => {
            return <View key={`${partTerm?.value}${index}`} style={{ marginVertical: 10 }}>
              <HelpText
                label={partTerm?.title ?? ''}
                helpText={partTerm?.help}
                style={styles.h5}
              />

              <TextInput
                keyboardType='numeric'
                style={styles.input}
                value={partTerms?.[partTerm?.value]}
                onChangeText={onPartTermsChange(partTerm?.value)}
              />
            </View>
          })
        }
        {/* <View style={{ marginVertical: 10 }}>
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
        </View> */}
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
  },
  h5: {
    fontSize: 12,
    lineHeight: 16,
    fontWeight: 'bold',
  },
})

export default TallyEditView;
