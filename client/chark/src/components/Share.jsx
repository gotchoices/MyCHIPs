import React, { useState, useRef } from 'react';

import { WebView } from 'react-native-webview';
import RNShare from 'react-native-share';
import QRCode from 'react-native-qrcode-svg';
import ViewShot from "react-native-view-shot";
import PropTypes from 'prop-types';
import {
  Text,
  View,
  StyleSheet,
  TouchableOpacity,
  TouchableWithoutFeedback,
  Linking,
} from 'react-native';

import { colors } from '../config/constants';

const Share = (props) => {
  const viewShotRef = useRef();
  const [activeTab, setActiveTab] = useState('qr');
  const url = url;

  const changeTab = (tab) => {
    return () => {
      setActiveTab(tab);
    }
  }

  const onShare = () => {
    let options = {};
    if (activeTab === 'qr') {
      viewShotRef.current.capture().then(uri => {
        options = {
          title: props.shareTitle,
          url: uri,
        };
        RNShare.open(options).then(console.log).catch(console.log);
      });
    } else if (activeTab === 'link') {
      const message = props.message;
      options = {
        title: 'Tally invitation',
        message,
      }

      RNShare.open(options).then(console.log).catch(console.log);
    }
  };

  const openExternalLink = (event) => {
    if (event.url && event.url.includes('mychips.org/tally')) {
      Linking.openURL(event.url)
      return false
    } else {
      return true
    }
  }

  return (
    <View style={styles.container}>
      <View style={styles.tab}>
        <TouchableWithoutFeedback
          onPress={changeTab('qr')}
        >
          <View style={[styles.tabItem, activeTab === 'qr' ? styles.activeTab : {}]}>
            <Text style={[styles.tabText, activeTab === 'qr' ? styles.activeText : {}]}>
              QR Code
            </Text>
          </View>
        </TouchableWithoutFeedback>

        <TouchableWithoutFeedback
          onPress={changeTab('link')}
        >
          <View style={[styles.tabItem, activeTab === 'link' ? styles.activeTab : {}]}>
            <Text style={[styles.tabText, activeTab === 'link' ? styles.activeText : {}]}>
              Link
            </Text>
          </View>
        </TouchableWithoutFeedback>
      </View>

      {
        activeTab === 'qr' && (
          <ViewShot ref={viewShotRef} options={{ format: "png", quality: 1.0 }}>
            <View style={styles.qrView}>
              <QRCode
                value={props.qrData}
                size={200}
              />
            </View>
          </ViewShot>
        )
      }

      {
        activeTab === 'link' && (
          <WebView
            originWhitelist={['*']}
            onShouldStartLoadWithRequest={openExternalLink}
            source={{
              html: `
              <html>
                <head><meta name="viewport" content="width=device-width, initial-scale=1.0"></head>
                <body>
                  <div style="display: flex; align-items: center; padding-top: 20">
                    <div>
                      ${props.linkHtml}
                    </div>
                  </div>
                </body>
              </html>
            `}}
          />
        )
      }

      <View style={styles.action}>
        <TouchableOpacity
          onPress={onShare}
        >
          <View style={styles.share}>
            <Text style={{ color: colors.white, fontWeight: 'bold', fontSize: 16 }}>Share</Text>
          </View>
        </TouchableOpacity>

      </View>
    </View>
  )
}

const actionItem = {
  borderWidth: 1,
  borderColor: colors.blue,
  marginHorizontal: '1%',
  justifyContent: 'center',
  alignItems: 'center',
  paddingVertical: 8,
  borderRadius: 5,
  marginBottom: 8,
}

const styles = StyleSheet.create({
  container: {
    flex: 1,
    width: '100%',
    backgroundColor: colors.white,
  },
  tab: {
    flexDirection: 'row',
    margin: 20,
  },
  tabItem: {
    padding: 8,
    width: '50%',
    borderWidth: 1,
    alignItems: 'center',
    justifyContent: 'center',
    borderColor: colors.blue,
  },
  tabText: {
    color: colors.black,
    fontWeight: '700',
  },
  activeTab: {
    backgroundColor: colors.blue,
  },
  activeText: {
    color: colors.white,
  },
  action: {
    paddingHorizontal: 10,
  },
  cancel: {
    ...actionItem,
  },
  share: {
    ...actionItem,
    backgroundColor: colors.blue,
  },
  qrView: {
    alignItems: 'center',
    paddingVertical: 32,
    backgroundColor: colors.white,
    marginVertical: 10,
  },
});

 Share.propTypes = {
   qrData: PropTypes.any.isRequired,
   linkHtml: PropTypes.string.isRequired,
   shareTitle: PropTypes.string.isRequired,
   // Message to share when shared through link
   message: PropTypes.string.isRequired,
 }

export default Share;
