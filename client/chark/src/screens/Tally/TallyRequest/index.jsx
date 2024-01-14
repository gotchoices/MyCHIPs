import React, { useState } from 'react'
import { View, StyleSheet } from 'react-native';

import RequestStart from './RequestStart';
import Certificates from './Certificates';
import CustomCertificate from './CustomCertificate';

const TallyRequest = (props) => {
  const invite = props.route?.params ?? {};

  const [tallyInfo, setTallyInfo] = useState(undefined);
  const [visibility, setVisibility] = useState({
    requestStart: true,
    certificateOptions: false,
    customCertificate: false,
    myCertificate: false,
    needCustom: true,
  })

  const showCorrespondingView = (view, needCustom = false) => {
    switch(view) {
      case 'certificateOptions':
        setVisibility({
          requestStart: false,
          certificateOptions: true,
          customCertificate: false,
          myCertificate: false,
          needCustom,
        })
        break;
      case 'customCertificate':
        setVisibility({
          requestStart: false,
          certificateOptions: false,
          customCertificate: true,
          myCertificate: false,
          needCustom,
        })
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
  }

  const onStart = () => {
    showCorrespondingView('certificateOptions');
  }

  const onItemPressed = (tally_ent, tally_seq) => {
    //showCorrespondingView('myCertificate');
    setTallyInfo({ tally_ent, tally_seq })
    showCorrespondingView('customCertificate', false);
  }

  const onCustomPressed = () => {
    showCorrespondingView('customCertificate', true);
  }

  const onCertificateDone = () => {
    showCorrespondingView('myCertificate');
  }

  return (
    <View style={styles.container}>
      {visibility.requestStart && (
        <RequestStart
          onStart={onStart}
          name={invite?.chad?.cid}
          agent={invite?.chad?.agent ?? ''}
          navigation={props.navigation}
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
  )
}

const styles = StyleSheet.create({
  container: {
    flex: 1,
    padding: 20,
  }
})

export default TallyRequest;
