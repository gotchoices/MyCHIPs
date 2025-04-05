import React, {useState, useMemo} from 'react';
import {
  View,
  Text,
  StyleSheet,
  TextInput,
  TouchableWithoutFeedback,
  TouchableOpacity,
  ScrollView,
} from 'react-native';
import {Picker} from '@react-native-picker/picker';
import moment from 'moment';
import { useSelector } from 'react-redux';

import HelpText from '../../components/HelpText';
import TallyReviewView from '../TallyReview/TallyReviewView';
import CertificateInformation from './CertificateInformation';
import ValidityIcon from '../../components/ValidityIcon';
import FontAwesome from 'react-native-vector-icons/FontAwesome';

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
  const onReSign = props.onReSign || null; // Function to handle re-signing the tally
  const onUpdateCert = props.onUpdateCert || null; // Function to handle updating the certificate

  // Get validation status from Redux
  const validityStatuses = useSelector(state => state.updateTally.validityStatuses || {});
  const tallyValidityStatus = tally?.tally_uuid ? validityStatuses[tally.tally_uuid] : undefined;
  
  // Also check for direct status on the tally object
  const validityStatus = tallyValidityStatus || tally.validityStatus;

  const {messageText} = useMessageText();

  const hasPartCert = !!tally?.part_cert;
  const hasHoldCert = !!tally?.hold_cert;

  const talliesMeText = messageText?.tallies_v_me?.col;
  const charkMsgText = messageText?.chark?.msg;
  const certText = messageText?.users_v_me?.col?.cert;

  const partName = Object.values(tally.part_cert?.name ?? {}).join(' ');
  const partChipAddress = hasPartCert
    ? `${tally.part_cert?.chad?.cuid ?? ''}:${
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
    ? `${tally.hold_cert?.chad?.cuid ?? ''}:${
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

        {/* Partner Group with tighter spacing */}
        <View style={styles.entityGroup}>
          {/* Partner Certificate Section */}
          {hasPartCert && (
            <CertificateInformation
              title={talliesMeText?.part_cert?.title ?? ''}
              name={partName}
              chipAddress={partChipAddress}
              onViewDetails={() =>
                onViewCertificate({
                  title: talliesMeText?.part_cert?.title ?? '',
                  cert: tally?.part_cert ?? {},
                })
              }
              certText={certText ?? {}}
              validityStatus={validityStatus}
            />
          )}
          
          {/* Partner Signature Section */}
          {tally.part_sig && (
            <View style={styles.signatureSection}>
              <View style={styles.signatureLabelContainer}>
                <HelpText
                  label={talliesMeText?.part_sig?.title ?? 'Partner Signature'}
                  helpText={talliesMeText?.part_sig?.help}
                />
                <View style={styles.iconGroup}>
                  {validityStatus && <ValidityIcon status={validityStatus} size={16} />}
                  {/* No repair button for partner signature as user can't fix partner's signature */}
                </View>
              </View>
              
              <ScrollView 
                horizontal={true} 
                style={styles.signatureScrollContainer}
              >
                <Text selectable={true} style={styles.signatureText}>
                  {tally.part_sig}
                </Text>
              </ScrollView>
            </View>
          )}
        </View>

        {/* Divider between partner and holder sections */}
        <View style={styles.sectionDivider} />

        {/* Holder Group with tighter spacing */}
        <View style={styles.entityGroup}>
          {/* Holder Certificate Section */}
          {!!tally?.hold_cert && (
            <CertificateInformation
              title={talliesMeText?.hold_cert?.title ?? ''}
              name={holdName}
              chipAddress={holdChipAddress}
              onViewDetails={() =>
                onViewCertificate({
                  title: charkMsgText?.certopts?.title,
                  cert: tally?.hold_cert ?? {},
                })
              }
              certText={certText ?? {}}
              validityStatus={validityStatus}
              onRepair={onUpdateCert}
            />
          )}
          
          {/* Holder Signature Section */}
          {tally.hold_sig && (
            <View style={styles.signatureSection}>
              <View style={styles.signatureLabelContainer}>
                <HelpText
                  label={talliesMeText?.hold_sig?.title ?? 'Holder Signature'}
                  helpText={talliesMeText?.hold_sig?.help}
                />
                <View style={styles.iconGroup}>
                  {validityStatus && <ValidityIcon status={validityStatus} size={16} />}
                  {validityStatus !== 'valid' && onReSign && (
                    <TouchableOpacity 
                      onPress={onReSign}
                      style={styles.repairButton}
                    >
                      <FontAwesome name="wrench" size={10} color={colors.white} />
                    </TouchableOpacity>
                  )}
                </View>
              </View>
              
              <ScrollView 
                horizontal={true} 
                style={styles.signatureScrollContainer}
              >
                <Text selectable={true} style={styles.signatureText}>
                  {tally.hold_sig}
                </Text>
              </ScrollView>
            </View>
          )}
        </View>
      </View>

      {/* Comments Section */}
      <View style={styles.sectionDivider} />
      <View style={styles.commentsSection}>
        
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
      </View>

      {/* Tally Identity Section */}
      <View style={styles.sectionDivider} />
      <View style={styles.identitySection}>
        
        <View style={styles.detailControl}>
          <HelpText
            label={talliesMeText?.tally_uuid?.title ?? ''}
            helpText={talliesMeText?.tally_uuid?.help}
          />
          <Text style={styles.inputValue}>{tally.tally_uuid}</Text>
        </View>
      </View>

      <View style={styles.detailControl}>
        <HelpText
          label={talliesMeText?.tally_date?.title ?? ''}
          helpText={talliesMeText?.tally_date?.help}
        />
        <Text style={styles.inputValue}>
          {moment(tally.tally_date).utc().format('YYYY-MM-DDTHH:mm:ss.SSS') + 'Z'}
        </Text>
      </View>

      {/* Trading Variables Section */}
      <View style={styles.sectionDivider} />
      <View style={styles.tradingVariablesSection}>
        
        {/* Bound field */}
        <View style={styles.detailControl}>
          <HelpText
            label={talliesMeText?.bound?.title ?? 'Bound'}
            helpText={talliesMeText?.bound?.help}
          />
          <Text style={styles.inputValue}>{tally.bound ?? 'N/A'}</Text>
        </View>
        
        {/* Target field */}
        <View style={styles.detailControl}>
          <HelpText
            label={talliesMeText?.target?.title ?? 'Target'}
            helpText={talliesMeText?.target?.help}
          />
          <Text style={styles.inputValue}>{tally.target ?? 'N/A'}</Text>
        </View>
        
        {/* Reward field */}
        <View style={styles.detailControl}>
          <HelpText
            label={talliesMeText?.reward?.title ?? 'Reward'}
            helpText={talliesMeText?.reward?.help}
          />
          <Text style={styles.inputValue}>{tally.reward ?? 'N/A'}</Text>
        </View>
        
        {/* Clutch field */}
        <View style={styles.detailControl}>
          <HelpText
            label={talliesMeText?.clutch?.title ?? 'Clutch'}
            helpText={talliesMeText?.clutch?.help}
          />
          <Text style={styles.inputValue}>{tally.clutch ?? 'N/A'}</Text>
        </View>
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
  validityContainer: {
    flexDirection: 'row',
    justifyContent: 'space-between',
    alignItems: 'center',
    padding: 12,
    backgroundColor: colors.gray5,
    borderWidth: 1,
    borderColor: colors.gray7,
    borderRadius: 8,
    marginTop: 4,
  },
  validityLabel: {
    fontSize: 14,
    fontWeight: '500',
    color: colors.black,
  },
  signatureLabelContainer: {
    flexDirection: 'row',
    justifyContent: 'space-between',
    alignItems: 'center',
    marginBottom: 4,
  },
  signatureScrollContainer: {
    backgroundColor: colors.gray5,
    borderWidth: 1,
    borderColor: colors.gray7,
    borderRadius: 8,
    padding: 8,
    maxHeight: 60,
  },
  signatureText: {
    fontFamily: 'monospace',
    fontSize: 12,
    color: colors.gray900,
  },
  iconGroup: {
    flexDirection: 'row',
    alignItems: 'center',
  },
  repairButton: {
    backgroundColor: colors.blue,
    width: 18,
    height: 18,
    borderRadius: 9,
    justifyContent: 'center',
    alignItems: 'center',
    marginLeft: 4,
  },
  // New styles for grouped layout
  entityGroup: {
    marginVertical: 0, // No extra margin within a group
  },
  signatureSection: {
    marginTop: 8, // Tight spacing between certificate and signature
    marginBottom: 4,
  },
  sectionDivider: {
    marginTop: 20,
    marginBottom: 15,
    borderBottomWidth: 1,
    borderBottomColor: colors.lightgray,
  },
  tradingVariablesSection: {
    marginBottom: 16,
  },
  identitySection: {
    marginBottom: 16,
  },
  commentsSection: {
    marginBottom: 16,
  },
});

export default TallyEditView;
