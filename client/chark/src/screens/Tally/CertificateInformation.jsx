import React from 'react';
import PropTypes from 'prop-types';

import {
  View,
  Text,
  StyleSheet,
  TouchableWithoutFeedback,
} from 'react-native';

import HelpText from '../../components/HelpText';

import { colors } from '../../config/constants';

const CertificateInformation = (props) => {
  return (
    <View style={styles.detailControl}>
      <HelpText
        label={props.title}
        style={styles.heading}
      />

      <View style={styles.certInfoWrapper}>
        <View style={styles.certInfo}>
          <HelpText
            label={'Formal Name'}
            style={styles.certInfoLabel}
          />

          <Text style={styles.certValue}>
            {props.name}
          </Text>
        </View>

        <View style={styles.certInfo}>
          <HelpText
            label={'Chip Address'}
            style={styles.certInfoLabel}
          />

          <Text style={styles.certValue}>
            {props.chipAddress}
          </Text>
        </View>

        <View style={styles.certInfo}>
          <HelpText
            label={'Email'}
            style={styles.certInfoLabel}
          />

          <Text style={styles.certValue}>
            {props.email}
          </Text>
        </View>

        <TouchableWithoutFeedback onPress={props.onViewDetails}>
          <Text style={styles.certOtherDetails}>
            View other details
          </Text>
        </TouchableWithoutFeedback>
      </View>
    </View>
  )
}

const styles = StyleSheet.create({
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
  certOtherDetails: {
    color: colors.blue3,
    textDecorationLine: 'underline',
  },
})

CertificateInformation.prototype = {
  title: PropTypes.string.isRequired,
  name: PropTypes.string.isRequired,
  chipAddress: PropTypes.string.isRequired,
  email: PropTypes.string.isRequired,
  onViewDetails: PropTypes.func.isRequired,
}

export default CertificateInformation;

