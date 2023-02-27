import React, { useState, useRef } from 'react';
import PropTypes from 'prop-types';
import { WebView } from 'react-native-webview';
import {
  Text,
  View,
  StyleSheet,
  TouchableOpacity,
  TouchableWithoutFeedback,
  Image,
  Linking,
} from 'react-native';
import Share from 'react-native-share';
import QRCode from 'react-native-qrcode-svg';

import { colors } from '../../../config/constants';

const ShareTally = (props) => {
  const tallyObj = props.json;
  const link = props.link;
  const ref = useRef();

  const [activeTab, setActiveTab] = useState('qr');

  const changeTab = (tab) => {
    return () => {
      setActiveTab(tab);
    }
  }

  const onShare = () => {
    let options = {};
    if(activeTab === 'qr') {
      qrtobase64().then(base64 => {
        options = {
          url: base64,
        }

        Share.open(options).then(console.log).catch(console.log);
      })
    } else if(activeTab === 'link') {
      options = {
        title: 'Tally invitation',
        message: link,
      }

      Share.open(options).then(console.log).catch(console.log);
    }
  };

  const onCancel = () => {
    props.onCancel()
  }

  const qrtobase64 = () => {
    return new Promise((resolve) => {
      ref.current.toDataURL((data) => {
        resolve('data:image/png;base64,'+ data)
      })
    })

  }

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
          <View style={{ alignItems: 'center', paddingVertical: 32,  }}>
            <QRCode
              value={JSON.stringify(props.json)}
              getRef={ref}
              size={200}
            />
          </View>
        )
      }

      {
        activeTab === 'link' && (
         <WebView
            originWhitelist={['*']}
            onShouldStartLoadWithRequest={openExternalLink}
            source={{ html: `
              <html>
                <head><meta name="viewport" content="width=device-width, initial-scale=1.0"></head>
                <body>
                  <div style="display: flex; align-items: center; padding-top: 20">
                    <div>
                      ${link}
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

        <TouchableOpacity
          onPress={onCancel}
        >
          <View style={styles.cancel}>
            <Text style={{ color: colors.blue, fontWeight: 'bold', fontSize: 16 }}>Cancel</Text>
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
  },
  tab: {
    flexDirection: 'row',
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
});

ShareTally.propTypes = {
  onCancel: PropTypes.func.isRequired,
  json: PropTypes.object,
  link: PropTypes.string,
}

export default ShareTally;
