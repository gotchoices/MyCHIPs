import React from 'react';
import PropTypes from 'prop-types';
import { 
  View,
  Text,
  StyleSheet,
} from 'react-native';

import HelpText from '../../../components/HelpText';

import { colors } from '../../../config/constants';

const CertificateItem = (props) => {
  return (
    <View style={styles.container}>
      <HelpText
        label={props.label}
        style={styles.label}
      />

      <Text style={styles.value}>
        {props.value}
      </Text>
    </View>
  )
}

const font = {
  fontFamily: 'inter',
  fontWeight: '500',
}

const styles = StyleSheet.create({
  container: {
    marginVertical: 8,
  },
  label: {
    ...font,
    fontSize: 12,
    color: colors.gray300,
  },
  value: {
    ...font,
    fontSize: 14,
    color: colors.black,
  },
});

CertificateItem.propTypes = {
  label: PropTypes.string.isRequired,
  value: PropTypes.string.isRequired,
};

export default CertificateItem;
