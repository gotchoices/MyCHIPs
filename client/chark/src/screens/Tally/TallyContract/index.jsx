import React, { useEffect, useState, useLayoutEffect } from 'react';
import { ActivityIndicator, StyleSheet, View, Alert } from 'react-native';
import { WebView } from 'react-native-webview';
import useSocket from '../../../hooks/useSocket';
import Button from '../../../components/Button';
import Share from 'react-native-share';
import RNFS from 'react-native-fs';

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
    showPDF();
  }, [tally_seq]);

  useEffect(() => {
    console.log("CONTRACT ==> ", contract);
  }, [contract])

  const showPDF = () => {
    setDownloading(true);
    const spec = {
      name: 'agree',
      view: 'mychips.tallies_v_me',
      data: {
        key: {
          tally_seq: tally_seq,
        },
        options: {
          format: 'url'
        }
      }
    };

    wm.request(`agree-${Math.random()}`, 'action', spec, (data, err) => {
      setDownloading(false);
      console.log("RESULT ==> ", `${data}`);
      console.log("ERROR ==> ", `${err}`);
      if (data) {
        setContract(data);
      }
    })
  }

  const onShare = () => {
    console.log("CONTRACT ==> ", contract);

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
            console.log("DOWNLOADED ==> ", JSON.stringify(result));
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
          console.log("SHARED ==> ", result);
        }).catch(ex => {
          setDownloading(false);
          console.log("EXCEPTION ==> ", JSON.stringify(ex));
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

  return <View style={styles.container}>
    <WebView
      startInLoadingState={true}
      scalesPageToFit={true}
      renderLoading={renderLoading}
      javaScriptEnabled={true}
      domStorageEnabled={true}
      style={styles.webView}
      source={{ uri: `https://docs.google.com/gview?embedded=true&url=${contract}` }}
    />
    <Button
      title='Share'
      onPress={onShare}
      style={{ borderRadius: 20, paddingHorizontal: 12, margin: 12 }}
      disabled={downloading}
    />
  </View>
}

const styles = StyleSheet.create({
  container: {
    flex: 1,
  },
  webView: {
    flex: 1,
  },
})

export default TallyContract;

