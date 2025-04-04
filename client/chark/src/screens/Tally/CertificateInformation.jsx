import React, { useMemo } from 'react';
import PropTypes from 'prop-types';

import {
  View,
  Text,
  StyleSheet,
  TouchableWithoutFeedback,
  TouchableOpacity,
} from 'react-native';
import FontAwesome from 'react-native-vector-icons/FontAwesome';

import HelpText from '../../components/HelpText';
import ValidityIcon from '../../components/ValidityIcon';

import { colors } from '../../config/constants';
import useMessageText from '../../hooks/useMessageText';

const CertificateInformation = (props) => {
  const certText = props.certText;
  const { messageText } = useMessageText();
  const charkText = messageText?.chark?.msg;

  const certValueText = useMemo(() => {
    return certText?.values?.reduce((acc, curr) => {
      acc[curr.value] = curr;
      return acc;
    }, {})
  }, [certText?.values])

  return (
    <View style={styles.detailControl}>
      <View style={styles.headingContainer}>
        <HelpText
          label={props.title}
          style={styles.heading}
        />
        <View style={styles.iconGroup}>
          {props.validityStatus && (
            <ValidityIcon status={props.validityStatus} size={16} />
          )}
          {props.validityStatus !== 'valid' && props.onRepair && (
            <TouchableOpacity 
              onPress={props.onRepair}
              style={styles.repairButton}
            >
              <FontAwesome name="wrench" size={10} color={colors.white} />
            </TouchableOpacity>
          )}
        </View>
      </View>

      <View style={styles.certInfoWrapper}>
        <TouchableWithoutFeedback onPress={props.onViewDetails}>
          <View style={styles.certWrapperTouchable}>
            <View style={styles.certInfo}>
              <HelpText
                label={certValueText?.name?.title ?? 'part_cert_name'}
                helpText={certValueText?.name?.help?? ''}
                style={styles.certInfoLabel}
              />

              <Text style={styles.certValue}>
                {props.name}
              </Text>
            </View>

            <View style={styles.certInfo}>
          <HelpText
            label={certValueText?.chad?.title ?? 'part_chad'}
            helpText={certValueText?.chad?.help}
            style={styles.certInfoLabel}
          />

          <Text style={styles.certValue}>
            {props.chipAddress}
          </Text>
        </View>

        {!!props.email && (
          <View style={styles.certInfo}>
            <HelpText
              label={certValueText?.email?.title ?? 'partner_or_holder_email'}
              helpText={certValueText?.email?.help}
              style={styles.certInfoLabel}
            />

            <Text style={styles.certValue}>
              {props.email}
            </Text>
          </View>
        )}
            
            {/* Chevron icon positioned in the top right of the wrapper */}
            <View style={styles.chevronContainer}>
              <FontAwesome name="angle-double-right" size={16} color={colors.blue3} />
            </View>
          </View>
        </TouchableWithoutFeedback>
      </View>
    </View>
  )
}

const styles = StyleSheet.create({
  headingContainer: {
    flexDirection: 'row',
    alignItems: 'center',
    justifyContent: 'space-between',
    marginBottom: 4,
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
  heading: {
    fontSize: 12,
    fontWeight: '500',
  },
  detailControl: {
    marginVertical: 10
  },
  certInfoWrapper: {
    backgroundColor: colors.gray5,
    borderWidth: 1,
    borderColor: colors.gray7,
    borderRadius: 8,
    padding: 16,
  },
  certInfo: {
    marginBottom: 12,
    fontFamily: 'inter',
  },
  certValue: {
    color: colors.black,
    fontSize: 12,
    fontWeight: '500',
    fontFamily: 'inter',
  },
  certInfoLabel: {
    fontWeight: '500',
    fontSize: 11,
    marginBottom: 0,
    color: colors.gray300,
  },
  certWrapperTouchable: {
    width: '100%',
    position: 'relative',
  },
  chevronContainer: {
    position: 'absolute',
    top: 8,
    right: 8,
  },
})

CertificateInformation.propTypes = {
  title: PropTypes.string.isRequired,
  name: PropTypes.string.isRequired,
  chipAddress: PropTypes.string.isRequired,
  email: PropTypes.string,
  onViewDetails: PropTypes.func.isRequired,
  onRepair: PropTypes.func,
  certText: PropTypes.any.isRequired,
  validityStatus: PropTypes.string
}

export default CertificateInformation;

