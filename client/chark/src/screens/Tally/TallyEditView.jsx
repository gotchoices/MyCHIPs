import React, { useState, useMemo } from 'react';
import {
  View,
  Text,
  StyleSheet,
  TextInput,
  TouchableWithoutFeedback,
} from 'react-native';
import { Picker } from '@react-native-picker/picker';
import moment from 'moment'

import HelpText from '../../components/HelpText';
import TallyReviewView from '../TallyReview/TallyReviewView';
import CertificateInformation from './CertificateInformation';

import EyeIcon from '../../../assets/svg/eye_icon.svg';
import { colors } from '../../config/constants';
import useMessageText from '../../hooks/useMessageText';

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
  const canEdit = tally.state === 'draft' || tally.state === 'P.draft';

  const { messageText } = useMessageText();
  const talliesText = messageText?.tallies;
  const holdTermsText = messageText?.terms_lang?.hold_terms?.values;
  const partTermsText = messageText?.terms_lang?.part_terms?.values;
  const hasPartCert = !!tally?.part_cert;
  const hasHoldCert = !!tally?.hold_cert;

  const partName= Object.values((tally.part_cert?.name ?? {})).join(' ')
  const partChipAddress = hasPartCert ? `${tally.part_cert?.chad?.cid ?? ''}-${tally.part_cert?.chad?.agent ?? ''}` : '';
  const partEmail = useMemo(() => {
    if(hasPartCert) {
      const found = (tally.part_cert?.connect ?? []).find(connect => connect.media === 'email')
      return found?.address ?? ''
    }

    return '';
  }, [hasPartCert, tally.part_cert?.connect])

  const holdName= Object.values((tally.hold_cert ?.name ?? {})).join(' ')
  const holdChipAddress = hasHoldCert ? `${tally.hold_cert?.chad?.cid ?? ''}-${tally.hold_cert?.chad?.agent ?? ''}` : '';
  const holdEmail = useMemo(() => {
    if(hasHoldCert) {
      const found = (tally.hold_cert?.connect ?? []).find(connect => connect.media === 'email')
      return found?.address ?? ''
    }

    return '';
  }, [hasHoldCert, tally.hold_cert?.connect])


  const onViewCertificate= (data) => {
    return () => props.navigation.navigate("TallyCertificate", { data });
  }

  return (
    <View style={{ paddingHorizontal: 10 }}>
      <TallyReviewView 
        tallyType={tallyType}
        setTallyType={setTallyType}
        partTerms={partTerms}
        holdTerms={holdTerms}
        partCert={tally?.part_cert ?? {}}
        holdCert={tally?.hold_cert ?? {}}
        onHoldTermsChange={onHoldTermsChange}
        onPartTermsChange={onPartTermsChange}
        canEdit={canEdit}
      />

      <View style={styles.detailControl}>
        <View style={styles.contractLabel}>
          <HelpText
            label={talliesText?.contract?.title ?? ''}
            helpText={talliesText?.contract?.help}
          />

        <TouchableWithoutFeedback
          onPress={props.onViewContract}
          style={{ marginBottom: 8 }}
        >
          <EyeIcon style={{ marginLeft: 8, marginBottom: 8 }}/>
        </TouchableWithoutFeedback>

        </View>

        {canEdit ? (
          <Picker
            mode="dropdown"
            style={{ backgroundColor: colors.gray5 }}
            selectedValue={contract}
            enabled={canEdit}
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
        ): (
          <Text style={styles.inputValue}>
            {contract}
          </Text>
        )}

        {hasPartCert && (
            <CertificateInformation
              title={'Partner Certificate Information'}
              name={partName}
              chipAddress={partChipAddress}
              email={partEmail}
              onViewDetails={onViewCertificate({ title: 'Partner Certificate', ...(tally?.part_cert ?? {} ) })}
            />
        )}

        {!!tally?.hold_cert && (
            <CertificateInformation
              title={'My Certificate Information'}
              name={holdName}
              chipAddress={holdChipAddress}
              email={holdEmail}
              onViewDetails={onViewCertificate({ title: 'My Certificate', ...(tally?.hold_cert ?? {} ) })}
            />
        )}

      </View>

      <View style={styles.detailControl}>
        <HelpText
          label={talliesText?.comment?.title ?? ''}
          helpText={talliesText?.comment?.help}
        />

        {canEdit ? (
          <TextInput
            multiline
            numberOfLines={4}
            value={comment}
            editable={canEdit}
            style={[styles.input, styles.comment]}
            onChangeText={setComment}
          />
        ): (
          <Text style={styles.inputValue}>
            {comment || 'N/A'}
          </Text>
        )}
      </View>

      <View style={styles.detailControl}>
        <HelpText
          label={talliesText?.tally_uuid?.title ?? ''}
          helpText={talliesText?.tally_uuid?.help}
        />

        <Text style={styles.inputValue}>
          {tally.tally_uuid}
        </Text>
      </View>

      <View style={styles.detailControl}>
        <HelpText
          label={talliesText?.tally_date?.title ?? ''}
          helpText={talliesText?.tally_date?.help}
        />
        <Text style={styles.inputValue}>
          {moment(tally.tally_date).format('MM/DD/YYYY,hh:mm')} 
        </Text>
      </View>
    </View>
  )
}

const styles = StyleSheet.create({
  detailControl: {
    marginTop:20,
    marginVertical: 10
  },
  contractLabel: {
    flexDirection: 'row',
    alignItems: 'center',
  },
  input: {
    padding: 10,
    borderColor: colors.gray,
    borderWidth: 1,
    borderRadius: 5,
    backgroundColor: colors.white,
  },
  certInfoWrapper: {
    backgroundColor: '#f2f2f2',
    borderWidth: 1,
    borderColor: '#dfdfdf',
    borderRadius: 8,
    padding: 16,
  },
  certInfo: {
    marginBottom: 12,
  },
  certInfoLabel: {
    fontSize: 11,
    marginBottom: 0,
    color: '#636363',
  },
  certOtherDetails: {
    color: '#155CEF',
    textDecorationLine: 'underline',
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
  inputValue: {
    color: 'black',
    fontSize: 12,
  }
})

export default TallyEditView;

