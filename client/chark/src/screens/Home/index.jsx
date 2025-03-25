import React, { useEffect, useState, useId } from 'react';
import { View, Linking, Modal } from 'react-native'
import qs from 'query-string';
import { useSelector } from 'react-redux';
import { useDispatch } from 'react-redux';

import Tally from '../Tally';

import { parse } from '../../utils/query-string';
import useSocket from '../../hooks/useSocket';
import { setPersonal } from '../../redux/profileSlice';
import useTitle from '../../hooks/useTitle'
import { LINK_TYPES, extractPathType, addUuidToUrl, parseSignkeyUrl } from '../../utils/deep-links';

import CenteredModal from '../../components/CenteredModal';
import UpdateCUID from '../UpdateCUID';
import { useCharkText } from "../../hooks/useLanguage";

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
      // Handle signkey URL with UUID to ensure uniqueness
      const uniqueSignkeyUrl = addUuidToUrl(signkeyUrl);
      
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
      
      // Extract path type to determine link type
      const pathType = extractPathType(url);
      
      // Check the path to determine link type
      if (pathType === LINK_TYPES.TICKET) {
        const obj = parse(url);
        connect({ ticket: obj });
      } else if (pathType === LINK_TYPES.INVITE) {
        const parsed = parseTallyInvitation(url);
        requestProposedTally(parsed);
      } else if (pathType === LINK_TYPES.PAY) {
        const parsed = qs.parseUrl(url);
        props.navigation.navigate('PaymentDetail', {
          distributedPayment: parsed.query,
        });
      } else if (pathType === LINK_TYPES.SIGNKEY) {
        // Add random UUID for uniqueness
        const uniqueSignkeyUrl = addUuidToUrl(url);
        
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
