import React, { useState } from 'react';
import { useDispatch  } from 'react-redux';
import PropTypes from 'prop-types';
import stringify from 'json-stable-stringify';
import {
  Alert,
} from 'react-native';

import Button from '../../components/Button';

import useSocket from '../../hooks/useSocket';
import { colors } from '../../config/constants';
import { createSignature } from '../../utils/message-signature';
import { acceptTally } from '../../services/tally';
import { setShowCreateSignatureModal } from '../../redux/profileSlice';
import { KeyNotFoundError } from '../../utils/Errors';
import { showError } from '../../utils/error';
import { comparePublicKey } from '../../services/tally';
import Toast from 'react-native-toast-message'

const AcceptButton = (props) => {
  const tally = props.tally;

  const dispatch = useDispatch();
  const { wm } = useSocket();

  const [accepting, setAccepting] = useState(false);

  const showCreateSignatureModal = () => {
    dispatch(setShowCreateSignatureModal(true));
  }

  const onAccept = async () => {
    if (!tally?.json_core) {
      Alert.alert("Tally can not be signed");
      return;
    }

    try {
      setAccepting(true);
      const message = stringify(tally.json_core)

      const tallyType = tally?.tally_type;
      const tallyPublicKey = tally?.json_core?.[tallyType]?.cert?.public;
      const isNewPublicKey = await comparePublicKey(tallyPublicKey)

      if(!isNewPublicKey) {
        return Toast.show({
          type: 'success',
          text1: 'New key cannot used for signing the tally',
        })
      }

      const signature = await createSignature(message);
      await acceptTally(wm, {
        signature,
        tally_ent: tally.tally_ent,
        tally_seq: tally.tally_seq,
      });

      props.postOffer?.();

    } catch(err) {
      if(err instanceof KeyNotFoundError) {
        showCreateSignatureModal();
      } else {
        showError(err);
      }

    } finally {
      setAccepting(false);
    }
  };

  return (
    <Button
      title={props?.text?.accept?.title ?? 'accept_text'}
      onPress={onAccept}
      disabled={accepting}
      textColor={colors.white}
      style={props.style ?? {}}
    />
  )
}

AcceptButton.propTypes = {
  style: PropTypes.any,
  tally: PropTypes.object.isRequired,
  postAccept: PropTypes.func,
}

export default AcceptButton;
