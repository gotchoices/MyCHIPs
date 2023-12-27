import React, { useEffect, useState, useLayoutEffect } from "react";
import {
  ActivityIndicator,
  StyleSheet,
  View,
  Alert,
  Text,
} from "react-native";
import { WebView } from "react-native-webview";
import Share from "react-native-share";
import RNFS from "react-native-fs";

import useSocket from "../../../hooks/useSocket";
import { getContract } from "../../../services/tally";

import FloatingActionButton from "../../../components/FloadingActionButton";
import { useRef } from "react";

const TallyContract = (props) => {
  const { tally_seq } = props.route?.params ?? {};
  const { wm } = useSocket();
  const [contract, setContract] = useState(null);
  const [downloading, setDownloading] = useState(false);
  const [hasError, setHasError] = useState(false);

  const webViewRef = useRef();

  useEffect(() => {
    const showPDF = async () => {
      setDownloading(true);

      getContract(wm, {
        tally_seq,
      })
        .then((data) => {
          setContract(data);
          setHasError(false);
        })
        .catch((err) => {
          setHasError(true);
        })
        .finally(() => {
          setDownloading(false);
        });
    };

    showPDF();
  }, [wm, tally_seq, setContract]);

  const onShare = () => {
    if (contract) {
      setDownloading(true);
      const downloadDest = `${RNFS.CachesDirectoryPath}/contract.pdf`;
      const downloadOptions = {
        fromUrl: contract,
        toFile: downloadDest,
      };

      RNFS.downloadFile(downloadOptions)
        .promise.then((result) => {
          if (result.statusCode === 200) {
            return downloadDest;
          }
          return "Failed to download";
        })
        .then((downloadPath) => {
          setDownloading(false);
          const shareOptions = {
            title: "Share Contract",
            message: "Please find the attached contract file.",
            url: `file://${downloadPath}`,
            type: "application/pdf",
          };

          return Share.open(shareOptions);
        })
        .then((result) => {})
        .catch((ex) => {
          setDownloading(false);
        });
    } else {
      Alert.alert("Error", "Contract not found.");
    }
  };

  const renderLoading = () => {
    return (
      <View style={styles.center}>
        <ActivityIndicator size={"large"} />
      </View>
    );
  };

  const injectedJs = `
    const meta = document.createElement('meta'); 
    meta.setAttribute('content', 'width=device-width, initial-scale=1, maximum-scale=1, user-scalable=0'); 
    meta.setAttribute('name', 'viewport');
    document.getElementsByTagName('head')[0].appendChild(meta); 
  `;

  return (
    <View style={styles.container}>
      {hasError ? (
        <View style={styles.center}>
          <Text style={{ fontSize: 14, fontWeight: "600" }}>
            Cannot load the content.
          </Text>
        </View>
      ) : contract ? (
        <View style={styles.webView}>
          <WebView
            ref={webViewRef}
            style={styles.webView}
            scalesPageToFit={false}
            javaScriptEnabled={true}
            domStorageEnabled={true}
            startInLoadingState={true}
            renderLoading={renderLoading}
            onLoad={() => setHasError(false)}
            injectedJavaScript={injectedJs}
            source={{
              uri: `https://docs.google.com/gview?embedded=true&url=${contract}`,
            }}
            onContentProcessDidTerminate={(syntheticEvent) => {
              this.refs.webview.reload();
            }}
            onLoadEnd={(data) => {
              const { nativeEvent } = data;
              const { title } = nativeEvent;

              if (!title.trim()) {
                webViewRef.current?.stopLoading();
                webViewRef.current?.reload();
              }
            }}
          />

          <FloatingActionButton
            onPress={onShare}
            type="share"
            disabled={downloading}
          />
        </View>
      ) : (
        <View style={styles.center}>{renderLoading()}</View>
      )}
    </View>
  );
};

const styles = StyleSheet.create({
  container: {
    flex: 1,
  },
  webView: {
    flex: 1,
    width: "100%",
    height: "100%",
  },
  center: {
    flex: 1,
    alignItems: "center",
    justifyContent: "center",
  },
});

export default TallyContract;
