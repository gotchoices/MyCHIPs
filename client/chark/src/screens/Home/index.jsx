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
import UpdateCID from '../UpdateCID';
import { useCharkText } from "../../hooks/useLanguage";

const connectionUri = new Set(['ticket', 'mychips.org/ticket'])
const tallyUri = new Set(['invite', 'mychips.org/invite'])
const payUri = new Set(['mychips.org/pay'])

const HomeScreen = (props) => {
  const { connectSocket, wm } = useSocket();
  const { invite, tallyInviteUrl, payUrl } = props.route?.params ?? {};
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
    const cid = personal?.cid;

    if (userId === cid && useId !== undefined && userId !== null && cid !== undefined && cid !== null) {
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
    }
  }, [tallyInviteUrl, payUrl])

  useEffect(() => {
    const handleLink = (url) => {
      const host = getLinkHost(url ?? '');

      if (connectionUri.has(host)) {
        const obj = parse(url);
        connect({ ticket: obj });
      } else if (tallyUri.has(host)) {
        const parsed = parseTallyInvitation(url);
        requestProposedTally(parsed)
      } else if(payUri.has(host)) {
        const parsed = qs.parseUrl(url);
        props.navigation.navigate('PaymentDetail', {
          distributedPayment: parsed.query,
        })
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
  const onSuccess = (cid) => {
    console.log("CID ==> ", cid);
    dispatch(setPersonal({
      ...personal,
      cid: cid,
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
        <UpdateCID
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
