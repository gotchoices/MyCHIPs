import React, { useEffect, useState, useId } from 'react';
import { View, Linking, Modal } from 'react-native'
import qs from 'query-string';
import { useSelector } from 'react-redux';
import { useDispatch } from 'react-redux';

import Tally from '../Tally';

import { parse } from '../../utils/query-string';
import { getLinkHost } from '../../utils/common';
import useSocket from '../../hooks/useSocket';
import { setPersonal } from '../../redux/profileSlice';
import useTitle from '../../hooks/useTitle'

import CenteredModal from '../../components/CenteredModal';
import UpdateCUID from '../UpdateCUID';
import { useCharkText } from "../../hooks/useLanguage";

const connectionUri = new Set(['ticket', 'mychips.org/ticket'])
const tallyUri = new Set(['invite', 'mychips.org/invite'])
const payUri = new Set(['mychips.org/pay'])
const signkeyUri = new Set(['mychips.org/signkey'])

const HomeScreen = (props) => {
  const { connectSocket, wm } = useSocket();
  const { invite, tallyInviteUrl, payUrl, signkeyUrl } = props.route?.params ?? {};
  const { user } = useSelector(state => state.currentUser);
  const { personal } = useSelector(state => state.profile);
  const dispatch  = useDispatch();

  const [visible, setVisible] = useState(false);

  // Common text, will be used by multiple screens
  const charkText = useCharkText(wm);
  const charkMsgText = charkText?.msg;

  useTitle(props.navigation, charkMsgText?.mychips?.title ?? 'Hello')

  const connect = (ticket) => {
    connectSocket(ticket);
  }

  useEffect(() => {
    const userId = user?.curr_eid;
    const cuid = personal?.cuid;

    if (userId === cuid && useId !== undefined && userId !== null && cuid !== undefined && cuid !== null) {
      showUpdateDialog();
    }
  }, [user, personal])

  useEffect(() => {
    if(tallyInviteUrl) {
      const parsed = parseTallyInvitation(tallyInviteUrl);
      requestProposedTally(parsed)
    } else if (invite) {
      requestProposedTally(invite)
    } else if(payUrl) {
      const parsed = qs.parseUrl(payUrl);
      props.navigation.navigate('PaymentDetail', {
        distributedPayment: parsed.query,
      })
    } else if(signkeyUrl) {
      console.log("Processing signkey URL from route params");
      // Handle signkey URL with UUID to ensure uniqueness
      const { v4: uuidv4 } = require('uuid');
      const uniqueSignkeyUrl = `${signkeyUrl}${signkeyUrl.includes('?') ? '&' : '?'}randomString=${uuidv4()}`;
      console.log("Created unique URL:", uniqueSignkeyUrl);
      
      props.navigation.navigate('Settings', {
        screen: 'KeyManagement',
        params: {
          signkeyUrl: uniqueSignkeyUrl,
          autoImport: true
        }
      });
    }
  }, [tallyInviteUrl, payUrl, signkeyUrl])

  useEffect(() => {
    const handleLink = (url) => {
      if (!url) return;
      
      console.log("Handling deep link URL:", url);
      
      // Extract path from URL using the same method as other functions in the app
      const pathWithoutParams = url?.split('?')?.[0] || '';
      const pathSegments = pathWithoutParams.split('/');
      const pathType = pathSegments[pathSegments.length - 1]; // Get the last segment
      
      console.log("Path type detected:", pathType);
      
      // Check the path to determine link type
      if (pathType === 'ticket') {
        const obj = parse(url);
        connect({ ticket: obj });
      } else if (pathType === 'invite') {
        const parsed = parseTallyInvitation(url);
        requestProposedTally(parsed);
      } else if (pathType === 'pay') {
        const parsed = qs.parseUrl(url);
        props.navigation.navigate('PaymentDetail', {
          distributedPayment: parsed.query,
        });
      } else if (pathType === 'signkey') {
        console.log("Processing signkey deep link");
        // Add random UUID for uniqueness
        const { v4: uuidv4 } = require('uuid');
        const uniqueSignkeyUrl = `${url}${url.includes('?') ? '&' : '?'}randomString=${uuidv4()}`;
        console.log("Created unique URL:", uniqueSignkeyUrl);
        
        props.navigation.navigate('Settings', {
          screen: 'KeyManagement',
          params: {
            signkeyUrl: uniqueSignkeyUrl,
            autoImport: true
          }
        });
      }
      
      return;
    }

    Linking.getInitialURL().then((url) => {
      handleLink(url);
    });

    const listener = Linking.addEventListener('url', ({ url }) => {
      handleLink(url);
    })

    return () => {
      listener.remove();
    };

  }, []);

  const showUpdateDialog = () => {
    setVisible(true);
  }

  const dismissUpdateDialog = () => {
    setVisible(false);
  }
  const onSuccess = (cuid) => {
    console.log("CUID ==> ", cuid);
    dispatch(setPersonal({
      ...personal,
      cuid: cuid,
    }))
    dismissUpdateDialog();
  }

  function requestProposedTally(invite) {
    setTimeout(() => {
      props.navigation.navigate("TallyRequest", invite);
    }, 100)
  }

  return (
    <>
      <View style={{ flex: 1, marginTop:-10 }}>
        <Tally navigation={props.navigation} />
      </View>

      <CenteredModal
        isVisible={visible}
        onClose={dismissUpdateDialog}
      >
        <UpdateCUID
          userId={user?.curr_eid}
          cancel={dismissUpdateDialog}
          success={onSuccess}
        />
      </CenteredModal>
    </>
  );
}

function parseTallyInvitation(url) {
  const parsed = qs.parseUrl(url);
  const query = parsed.query;

  const token = query.token;

  if (query.chad) {
    try {
      const chad = JSON.parse(query.chad);

      return {
        token,
        chad,
      }
    } catch {
      return;
    }
  }
}

export default HomeScreen;
