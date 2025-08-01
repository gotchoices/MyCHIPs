import React, {useState} from 'react';
import {useDispatch} from 'react-redux';
import {View, StyleSheet} from 'react-native';

import RequestStart from './RequestStart';
import Certificates from './Certificates';
import CustomCertificate from './CustomCertificate';

import useMessageText from '../../../hooks/useMessageText';
import {startRequest} from '../../../redux/certificateTalliesSlice';
import {promptBiometrics} from '../../../services/biometrics';

const TallyRequest = props => {
  const invite = props.route?.params ?? {};
  const dispatch = useDispatch();

  const [tallyInfo, setTallyInfo] = useState(undefined);
  const [visibility, setVisibility] = useState({
    requestStart: true,
    certificateOptions: false,
    customCertificate: false,
    myCertificate: false,
    needCustom: true,
  });

  const {messageText} = useMessageText();
  const talliesMeMessageText = messageText?.tallies_v_me?.msg;
  const talliesMeColText = messageText?.tallies_v_me?.col;
  const charkMessageText = messageText?.chark?.msg;

  const commonText = {
    invited: talliesMeMessageText?.invited,
    next: charkMessageText?.next,
    hold_cert: talliesMeColText?.hold_cert,
  };

  const setCertificateOptionTrue = needCustom => {
    setVisibility({
      requestStart: false,
      certificateOptions: true,
      customCertificate: false,
      myCertificate: false,
      needCustom,
    });
  };

  const setCustomCertificateTrue = needCustom => {
    setVisibility({
      requestStart: false,
      certificateOptions: false,
      customCertificate: true,
      myCertificate: false,
      needCustom,
    });
  };

  const biometricsAuth = async needCustom => {
    await promptBiometrics('Use biometrics for certificate management');

    setCustomCertificateTrue(needCustom);
  };

  const showCorrespondingView = (view, needCustom = false) => {
    switch (view) {
      case 'certificateOptions':
        setCertificateOptionTrue(needCustom);

        break;
      case 'customCertificate':
        biometricsAuth(needCustom);

        break;
        //case 'myCertificate':
        //setVisibility({
        //requestStart: false,
        //certificateOptions: false,
        //customCertificate: false,
        //myCertificate: true,
        //needCustom: false,
        //})
        break;
      default:
        break;
    }
  };

  const onStart = () => {
    dispatch(startRequest());
    showCorrespondingView('certificateOptions');
  };

  const onItemPressed = (tally_ent, tally_seq) => {
    //showCorrespondingView('myCertificate');
    setTallyInfo({tally_ent, tally_seq});
    showCorrespondingView('customCertificate', false);
  };

  const onCustomPressed = () => {
    showCorrespondingView('customCertificate', true);
  };

  const onCertificateDone = () => {
    showCorrespondingView('myCertificate');
  };

  return (
    <View style={styles.container}>
      {visibility.requestStart && (
        <RequestStart
          onStart={onStart}
          name={invite?.chad?.cuid}
          agent={invite?.chad?.agent ?? ''}
          navigation={props.navigation}
          commonText={commonText}
        />
      )}

      {visibility.certificateOptions && (
        <Certificates
          onCustomPressed={onCustomPressed}
          onItemPressed={onItemPressed}
          tally_ent={tallyInfo?.tally_ent}
          tally_seq={tallyInfo?.tally_seq}
        />
      )}

      {visibility.customCertificate && (
        <CustomCertificate
          navigation={props.navigation}
          cert={invite}
          onDone={onCertificateDone}
          tally_ent={tallyInfo?.tally_ent}
          tally_seq={tallyInfo?.tally_seq}
          needCustom={visibility.needCustom}
          showCorrespondingView={showCorrespondingView}
        />
      )}

      {/*}
    {visibility.myCertificate && (
        <MyCertificate 
          sendCertificate={sendCertificate}
          showCorrespondingView={showCorrespondingView}
        />
      )}
    {*/}
    </View>
  );
};

const styles = StyleSheet.create({
  container: {
    flex: 1,
    padding: 20,
  },
});

export default TallyRequest;
