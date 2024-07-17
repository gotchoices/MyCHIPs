import React, {useState, useMemo} from 'react';
import {
  View,
  Text,
  StyleSheet,
  TextInput,
  TouchableWithoutFeedback,
} from 'react-native';
import {Picker} from '@react-native-picker/picker';
import moment from 'moment';

import HelpText from '../../components/HelpText';
import TallyReviewView from '../TallyReview/TallyReviewView';
import CertificateInformation from './CertificateInformation';

import EyeIcon from '../../../assets/svg/eye_icon.svg';
import {colors} from '../../config/constants';
import useMessageText from '../../hooks/useMessageText';
import {promptBiometrics} from '../../services/biometrics';

const TallyEditView = props => {
  const tally = props.tally;
  const tallyType = props.tallyType;
  const contract = props.contract;
  const holdTerms = props.holdTerms;
  const partTerms = props.partTerms;
  const comment = props.comment;
  const setComment = props?.setComment;
  const onHoldTermsChange = props.onHoldTermsChange;
  const onPartTermsChange = props.onPartTermsChange;
  const setTallyType = props.setTallyType;
  const setContract = props.setContract;
  const tallyContracts = props.tallyContracts ?? [];
  const canEdit = tally.state === 'draft' || tally.state === 'P.draft';

  const {messageText} = useMessageText();

  const hasPartCert = !!tally?.part_cert;
  const hasHoldCert = !!tally?.hold_cert;

  const talliesMeText = messageText?.tallies_v_me?.col;
  const charkMsgText = messageText?.chark?.msg;
  const certText = messageText?.users_v_me?.col?.cert;

  const partName = Object.values(tally.part_cert?.name ?? {}).join(' ');
  const partChipAddress = hasPartCert
    ? `${tally.part_cert?.chad?.cuid ?? ''}-${
        tally.part_cert?.chad?.agent ?? ''
      }`
    : '';
  const partEmail = useMemo(() => {
    if (hasPartCert) {
      const found = (tally.part_cert?.connect ?? []).find(
        connect => connect.media === 'email',
      );
      return found?.address ?? '';
    }

    return '';
  }, [hasPartCert, tally.part_cert?.connect]);

  const holdName = Object.values(tally.hold_cert?.name ?? {}).join(' ');
  const holdChipAddress = hasHoldCert
    ? `${tally.hold_cert?.chad?.cuid ?? ''}-${
        tally.hold_cert?.chad?.agent ?? ''
      }`
    : '';
  const holdEmail = useMemo(() => {
    if (hasHoldCert) {
      const found = (tally.hold_cert?.connect ?? []).find(
        connect => connect.media === 'email',
      );
      return found?.address ?? '';
    }

    return '';
  }, [hasHoldCert, tally.hold_cert?.connect]);

  const onCommentChange = text => {
    setComment?.(text);
  };

  const onContractChange = item => {
    setContract(item);
  };
  console.log(tallyContracts);

  const onViewCertificate = async args => {
    try {
      await promptBiometrics('Use biometrics to view certificate');

      props.navigation.navigate('TallyCertificate', {
        title: args.title,
        cert: args.cert,
        state: tally.state,
        tally_seq: tally.tally_seq,
        tally_ent: tally.tally_ent,
      });
    } catch (err) {
      alert(err);
    }
  };

  return (
    <View style={{paddingHorizontal: 10}}>
      <TallyReviewView
        tallyType={tallyType}
        setTallyType={setTallyType}
        partTerms={partTerms}
        holdTerms={holdTerms}
        partCert={tally.part_cert ?? {}}
        holdCert={tally.hold_cert ?? {}}
        onHoldTermsChange={onHoldTermsChange}
        onPartTermsChange={onPartTermsChange}
        canEdit={canEdit}
      />

      <View style={styles.detailControl}>
        <View style={styles.contractLabel}>
          <HelpText
            label={talliesMeText?.contract?.title ?? ''}
            helpText={talliesMeText?.contract?.help}
          />

          <TouchableWithoutFeedback
            onPress={props.onViewContract}
            style={{marginBottom: 8}}>
            <View style={{paddingVertical: 4, paddingHorizontal: 5}}>
              <EyeIcon style={{marginBottom: 4}} />
            </View>
          </TouchableWithoutFeedback>
        </View>

        {canEdit ? (
          <View style={styles.container}>
            <Text style={[styles.inputValue]}>Select contract</Text>

            <Picker
              mode="dropdown"
              selectedValue={contract}
              enabled={canEdit}
              onValueChange={onContractChange}>
              {tallyContracts.map(tallyContract => (
                <Picker.Item
                  key={tallyContract.name}
                  label={tallyContract.title}
                  value={tallyContract.rid}
                />
              ))}
            </Picker>
          </View>
        ) : (
          <Text style={styles.inputValue}>{contract}</Text>
        )}

        {hasPartCert && (
          <CertificateInformation
            title={talliesMeText?.part_cert?.title ?? ''}
            name={partName}
            chipAddress={partChipAddress}
            email={partEmail}
            onViewDetails={() =>
              onViewCertificate({
                title: talliesMeText?.part_cert?.title ?? '',
                cert: tally?.part_cert ?? {},
              })
            }
            certText={certText ?? {}}
          />
        )}

        {!!tally?.hold_cert && (
          <CertificateInformation
            title={talliesMeText?.hold_cert?.title ?? ''}
            name={holdName}
            chipAddress={holdChipAddress}
            email={holdEmail}
            onViewDetails={() =>
              onViewCertificate({
                title: charkMsgText?.certopts?.title,
                cert: tally?.hold_cert ?? {},
              })
            }
            certText={certText ?? {}}
          />
        )}
      </View>

      <View style={styles.detailControl}>
        <HelpText
          label={talliesMeText?.comment?.title ?? ''}
          helpText={talliesMeText?.comment?.help}
        />

        {canEdit ? (
          <TextInput
            multiline
            numberOfLines={4}
            value={comment}
            editable={canEdit}
            style={[styles.input, styles.comment]}
            onChangeText={onCommentChange}
          />
        ) : (
          <Text style={styles.inputValue}>{comment || 'N/A'}</Text>
        )}
      </View>

      <View style={styles.detailControl}>
        <HelpText
          label={talliesMeText?.tally_uuid?.title ?? ''}
          helpText={talliesMeText?.tally_uuid?.help}
        />

        <Text style={styles.inputValue}>{tally.tally_uuid}</Text>
      </View>

      <View style={styles.detailControl}>
        <HelpText
          label={talliesMeText?.tally_date?.title ?? ''}
          helpText={talliesMeText?.tally_date?.help}
        />
        <Text style={styles.inputValue}>
          {moment(tally.tally_date).format('MM/DD/YYYY,hh:mm')}
        </Text>
      </View>
    </View>
  );
};

const styles = StyleSheet.create({
  detailControl: {
    marginTop: 20,
    marginVertical: 10,
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
  },
  container: {
    padding: 16,
    borderWidth: 1,
    borderRadius: 8,
    borderColor: colors.gray7,
    backgroundColor: colors.gray5,
  },
});

export default TallyEditView;
