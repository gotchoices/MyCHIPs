import React from 'react'
import { View } from 'react-native'
import PropTypes from 'prop-types';

import CertificateItem from './CertificateItem';

const DefaultCertificate = (props) => {
  return (
    <View>
      <CertificateItem
        label={'Formal Name'}
        value={props.name}
      />

      <CertificateItem
        label={'CID'}
        value={props.cid}
      />

      <CertificateItem
        label={'Email'}
        value={props.email}
      />

      <CertificateItem
        label={'Agent'}
        value={props.agent}
      />
    </View>
  )
}

DefaultCertificate.proptypes = {
  name: PropTypes.string.isRequired,
  cid: PropTypes.string.isRequired,
  email: PropTypes.string.isRequired,
  agent: PropTypes.string.isRequired,
};

export default DefaultCertificate;
