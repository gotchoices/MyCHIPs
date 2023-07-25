import React, { useEffect, useState } from 'react';
import { View, Linking } from 'react-native'
import qs from 'query-string';
import Toast from 'react-native-toast-message';

import Tally from '../Tally';

import { parse } from '../../utils/query-string';
import { getLinkHost } from '../../utils/common';
import useSocket from '../../hooks/useSocket';
import useCurrentUser from '../../hooks/useCurrentUser';
import CenteredModal from '../../components/CenteredModal';
import UpdateCID from '../UpdateCID';
import useProfile from '../../hooks/useProfile';
import { useId } from 'react';

const connectionUri = new Set(['connect', 'mychips.org/connect'])
const tallyUri = new Set(['tally', 'mychips.org/tally'])

const HomeScreen = (props) => {
  const { connectSocket, wm } = useSocket();
  const { ticket } = props.route?.params ?? {};
  const { user } = useCurrentUser();
  const { personal, setPersonal } = useProfile();

  const [visible, setVisible] = useState(false);

  const connect = (ticket) => {
    connectSocket(ticket);
  }

  useEffect(() => {
    const userId = user?.curr_eid;
    const cid = personal?.cid;
    console.log("USER_ID ==> ", userId);
    console.log("PERSONAL ==> ", cid);

    if (userId === cid && useId !== undefined && userId !== null && cid !== undefined && cid !== null) {
      showUpdateDialog();
    }
  }, [user, personal])

  useEffect(() => {
    if (ticket) {
      requestProposedTally(ticket)
    }
  }, [ticket?.token])

  useEffect(() => {
    const handleLink = (url) => {
      const host = getLinkHost(url ?? '');

      if (connectionUri.has(host)) {
        const obj = parse(url);
        connect({ ticket: obj });
      } else if (tallyUri.has(host)) {
        const parsed = parseTallyInvitation(url);
        requestProposedTally(parsed)
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
    setPersonal({
      ...personal,
      cid: cid,
    });
    dismissUpdateDialog();
  }
  function requestProposedTally(ticket) {
    const spec = {
      view: 'mychips.ticket_process',
      params: [ticket],
    }

    Toast.show({
      type: 'info',
      text1: 'Processing tally ticket...',
    });

    wm.request('_process_tally', 'select', spec, (data, err) => {
      if (err) {
        Toast.show({
          type: 'error',
          text1: err.message ?? 'Error processing tally ticket.',
        })
      } else if (data?.[0]?.ticket_process) {
        Toast.show({
          type: 'success',
          text1: 'Tally ticket processed.'
        })
      } else {
        Toast.show({
          type: 'error',
          text1: 'Tally ticket process failed.'
        })
      }
    });
  }

  return (
    <>
      <View style={{ flex: 1 }}>
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
