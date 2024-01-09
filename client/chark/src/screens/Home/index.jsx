import React, { useEffect, useState, useId } from 'react';
import { View, Linking, Modal } from 'react-native'
import qs from 'query-string';
import Toast from 'react-native-toast-message';
import { useSelector } from 'react-redux';

import Tally from '../Tally';

import { parse } from '../../utils/query-string';
import { getLinkHost } from '../../utils/common';
import useSocket from '../../hooks/useSocket';
import { setPersonal } from '../../redux/profileSlice';

import CenteredModal from '../../components/CenteredModal';
import UpdateCID from '../UpdateCID';
import { UpdateHoldCert } from '../Tally/TallyPreview/UpdateHoldCert';

const connectionUri = new Set(['ticket', 'mychips.org/ticket'])
const tallyUri = new Set(['invite', 'mychips.org/invite'])

const HomeScreen = (props) => {
  const { connectSocket, wm } = useSocket();
  const { invite } = props.route?.params ?? {};
  const { user } = useSelector(state => state.currentUser);
  const { personal } = useSelector(state => state.profile);

  const [visible, setVisible] = useState(false);
  const [updateCertVisible, setUpdateCertVisible] = useState(false);
  const [tallyProcess, setTallyProcess] = useState(undefined);

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
    if (invite) {
      requestProposedTally(invite)
    }
  }, [invite?.token])

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

  const onShowUpdateCert = () => {
    setUpdateCertVisible(true);
  }

  const onDismissUpdateCert = () => {
    setUpdateCertVisible(false);
  }

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

  function startProcessTally(partCert) {
    const spec = {
      view: 'mychips.ticket_process',
      params: [{ ...tallyProcess, part_cert: partCert }],
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
      <CenteredModal
        isVisible={updateCertVisible}
        onClose={onDismissUpdateCert}
      >
        <UpdateHoldCert
          onDismiss={onDismissUpdateCert}
          onUpdateCert={(data) => {
            onDismissUpdateCert();
            startProcessTally(data);
          }}
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
