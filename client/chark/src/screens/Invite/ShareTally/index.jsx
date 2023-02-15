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
} from 'react-native';
import Share from 'react-native-share';
import QRCode from 'react-native-qrcode-svg';

import { colors } from '../../../config/constants';

const ShareTally = (props) => {
  const tallyObj = props.tally;
  const ref = useRef();

  const [activeTab, setActiveTab] = useState('qr');
  let link = '';

  if(tallyObj?.tally) {
    const tally = tallyObj.tally;
    link = `https://mychips.org/tally-accept?token=${tally.token}&chad=${JSON.stringify(tally.chad)}`;
  }

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
        resolve('data:image/png;base64,'+data)
      })
    })

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
              value={JSON.stringify(props.tally)}
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
            source={{ html: `
              <html>
                <head><meta name="viewport" content="width=device-width, initial-scale=1.0"></head>
                <body>
                  <div style="display: flex; align-items: center; padding-top: 20">
                    <div>
                      <a href="${link}">
                        TIN
                      </a>

                      <p>
                        TIL; ${tallyObj?.tally?.expires} 
                      </p>
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
  tally: PropTypes.object,
}

export default ShareTally;
