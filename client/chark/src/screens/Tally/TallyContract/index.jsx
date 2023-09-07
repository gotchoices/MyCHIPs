import React, { useEffect, useState, useLayoutEffect } from 'react';
import { ActivityIndicator, StyleSheet, View, Alert } from 'react-native';
import { WebView } from 'react-native-webview';
import Share from 'react-native-share';
import RNFS from 'react-native-fs';

import useSocket from '../../../hooks/useSocket';
import { getContract } from '../../../services/tally';

import Button from '../../../components/Button';
import FloatingActionButton from '../../../components/FloadingActionButton';

const TallyContract = (props) => {
  const { tally_seq } = props.route?.params ?? {};
  const { wm } = useSocket();
  const [contract, setContract] = useState(null);
  const [downloading, setDownloading] = useState(false);

  /* useLayoutEffect(() => {
    props.navigation.setOptions({
      headerRight: () => (
        <Button
          title='Share'
          onPress={onShare}
          style={{ borderRadius: 20, paddingHorizontal: 12 }}
          disabled={downloading}
        />
      ),
    });
  }, [props.navigation, downloading]); */

  useEffect(() => {
    const showPDF = async () => {
      setDownloading(true);

      getContract(wm, {
        tally_seq
      }).then((data) => {
        setContract(data);
      }).catch(console.log).finally(() => {
        setDownloading(false);
      })
    }

    showPDF();
  }, [wm, tally_seq, setContract]);

  useEffect(() => {
  }, [contract])

  const onShare = () => {
    if (contract) {
      setDownloading(true);
      const downloadDest = `${RNFS.CachesDirectoryPath}/contract.pdf`;
      const downloadOptions = {
        fromUrl: contract,
        toFile: downloadDest,
      }

      RNFS.downloadFile(downloadOptions).promise
        .then(result => {
          if (result.statusCode === 200) {
            return downloadDest;
          }
          return "Failed to download";
        }).then(downloadPath => {
          setDownloading(false);
          const shareOptions = {
            title: 'Share Contract',
            message: 'Please find the attached contract file.',
            url: `file://${downloadPath}`,
            type: 'application/pdf',
          };
          return Share.open(shareOptions);
        }).then(result => {
        }).catch(ex => {
          setDownloading(false);
        });
    } else {
      Alert.alert("Error", "Contract not found.");
    }
  }

  const renderLoading = () => {
    return <View style={{ flex: 1, justifyContent: 'center', alignItems: 'center' }}>
      <ActivityIndicator size={'large'} />
    </View>
  }

  const injectedJs = `
    const meta = document.createElement('meta'); 
    meta.setAttribute('content', 'width=device-width, initial-scale=1, maximum-scale=1, user-scalable=0'); 
    meta.setAttribute('name', 'viewport');
    document.getElementsByTagName('head')[0].appendChild(meta); 
  `;

  return <View style={styles.container}>
    <WebView
      injectedJavaScript={injectedJs} 
      scalesPageToFit={false}
      startInLoadingState={true}
      renderLoading={renderLoading}
      javaScriptEnabled={true}
      domStorageEnabled={true}
      style={styles.webView}
      source={{ 
        uri: `https://docs.google.com/gview?embedded=true&url=${contract}`
      }}
    />
    
<FloatingActionButton onPress={onShare} type='share'  disabled={downloading}/>
  </View>
}

const styles = StyleSheet.create({
  container: {
    flex: 1,
  },
  webView: {
    flex: 1,
    width:"100%",
    height:"100%"
  },
})

export default TallyContract;

