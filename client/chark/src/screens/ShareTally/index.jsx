import React, { useState, useRef, useMemo, useEffect } from 'react';
import { WebView } from 'react-native-webview';
import {
  Text,
  View,
  StyleSheet,
  TouchableOpacity,
  TouchableWithoutFeedback,
  Linking,
} from 'react-native';
import Share from 'react-native-share';
import QRCode from 'react-native-qrcode-svg';
import ViewShot from "react-native-view-shot";

import { colors, qrType } from '../../config/constants';
import useSocket from '../../hooks/useSocket';
import { request } from '../../services/request';
import { random } from '../../utils/common';
import useMessageText from '../../hooks/useMessageText';

const ShareTally = (props) => {
  const tally_id = props.route?.params?.tally_id;
  const viewShotRef = useRef();
  const { wm } = useSocket();
  const { messageText } = useMessageText();
  const charkText = messageText?.chark?.msg;

  const [invite, setInvite] = useState();
  const [activeTab, setActiveTab] = useState('qr');

  const tallyObj = invite?.json;
  const linkHtml = invite?.link;
  const tallyUrl = tallyObj?.url;

  useEffect(() => {
    const spec = {
      name: 'invite',
      view: 'mychips.tallies_v_me',
      data: {
        keys: [{ tally_seq: tally_id }],
        options: {
          reuse: true,
          format: ['json', 'link']
        }
      }
    }

    request(wm, `_invite_ref_json_${random(1000)}`, 'action', spec).then((data) => {
      const json = data?.[0];
      const link = data?.[1];

      setInvite({
        json,
        link
      })
    }).catch((e) => {
      console.log("Sharing Exception", e);
    });
  }, [tally_id])

  const qrData = useMemo(() => {
    return JSON.stringify({ invite: tallyObj?.invite ?? {} });
    //return JSON.stringify({
      //type: qrType.tally,
      //ticket: tallyObj?.invite,
    //});
  }, [tallyObj?.invite])

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
          title: 'Tally invitation',
          url: uri,
        };
        Share.open(options).then(console.log).catch(console.log);
      });
    } else if (activeTab === 'link') {
      const expires = tallyObj?.ticket?.expires;
      const date = expires ? `:${new Date(expires).toString()}` : ''
      const message = `${tallyObj.title} \n\n${tallyUrl} \n\n${tallyObj.message} ${expires ? date : ''}`;
      options = {
        title: 'Tally invitation',
        message,
      }

      Share.open(options).then(console.log).catch(console.log);
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

  if(!invite) {
    return false;
  }

  return (
    <View style={styles.container}>
      <View style={styles.tab}>
        <TouchableWithoutFeedback
          onPress={changeTab('qr')}
        >
          <View style={[styles.tabItem, activeTab === 'qr' ? styles.activeTab : {}]}>
            <Text style={[styles.tabText, activeTab === 'qr' ? styles.activeText : {}]}>
              {charkText?.qr?.title}
            </Text>
          </View>
        </TouchableWithoutFeedback>

        <TouchableWithoutFeedback
          onPress={changeTab('link')}
        >
          <View style={[styles.tabItem, activeTab === 'link' ? styles.activeTab : {}]}>
            <Text style={[styles.tabText, activeTab === 'link' ? styles.activeText : {}]}>
              {charkText?.link?.title}
            </Text>
          </View>
        </TouchableWithoutFeedback>
      </View>

      {
        activeTab === 'qr' && (
          <ViewShot ref={viewShotRef} options={{ format: "png", quality: 1.0 }}>
            <View style={styles.qrView}>
              <QRCode
                value={qrData}
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
                      ${linkHtml}
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
            <Text style={{ color: colors.white, fontWeight: 'bold', fontSize: 16 }}>{charkText?.share?.title}</Text>
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

// ShareTally.propTypes = {
//   onCancel: PropTypes.func.isRequired,
//   json: PropTypes.object,
//   link: PropTypes.string,
// }

export default ShareTally;
