import React, {useMemo, useEffect} from 'react';
import {View, Text, StyleSheet} from 'react-native';
import PropTypes from 'prop-types';

import Header from './Header';
import Button from '../../../components/Button';
import BackIcon from '../../../../assets/svg/ic_back.svg';
import DefaultCertificate from '../TallyCertificate/DefaultCertificate';

import {colors} from '../../../config/constants';
import {promptBiometrics} from '../../../services/biometrics';

const MyCertificate = props => {
  const onBack = () => {
    //if(props.fromCustom) {
    //props.showCorrespondingView('customCertificate')
    //} else {
    props.showCorrespondingView('certificateOptions');
    //}
  };

  return (
    <View style={styles.container}>
      <Header headerText="My Certificate">
        <BackIcon onPress={onBack} />
      </Header>

      <View style={styles.content}>
        <DefaultCertificate
          name={'Joe Anderson'}
          cid={'p111'}
          email={'alex@gmail.com'}
          agent={'FKa-cxeWgnnqUp3lpsdlsk708xkDLSlklasdfLdsfD'}
        />

        <Button
          title="Send Certificate"
          onPress={async () => {
            try {
              await promptBiometrics('Use biometrics to send your certificate');
              
              props.sendCertificate();
            } catch (err) {
              alert(err);
            }
          }}
        />
      </View>
    </View>
  );
};

const styles = StyleSheet.create({
  container: {
    flex: 1,
  },
  content: {
    flex: 1,
    justifyContent: 'space-between',
    marginTop: 40,
  },
  header: {
    flexDirection: 'row',
    justifyContent: 'center',
  },
  headerIcon: {
    position: 'absolute',
    left: 0,
    top: -3,
  },
  headerText: {
    fontFamily: 'inter',
    fontSize: 18,
    fontWeight: '500',
    color: colors.black,
  },
});

MyCertificate.propTypes = {
  sendCertificate: PropTypes.func.isRequired,
  fromCustom: PropTypes.bool.isRequired,
  showCorrespondingView: PropTypes.func.isRequired,
};

export default MyCertificate;
