import React, { useState } from 'react';
import { useDispatch } from 'react-redux';
import {
  Alert,
  StyleSheet,
} from 'react-native';
import PropTypes from 'prop-types';
import stringify from 'json-stable-stringify';

import Button from '../../../components/Button';

import useSocket from '../../../hooks/useSocket';
import { acceptChit } from '../../../services/chit';
import { createSignature } from '../../../utils/message-signature';
import { setShowCreateSignatureModal } from '../../../redux/profileSlice';
import { showError } from '../../../utils/error';

const AcceptButton = (props) => {
  const { wm } = useSocket();
  const [disabled, setDisabled] = useState(false);
  const dispatch = useDispatch();

  const showCreateSignatureModal = () => {
    dispatch(setShowCreateSignatureModal(true));
  }

  const onAccept = async () => {
    const message = stringify(props.json);
    setDisabled(true);
    try {
      const signature = await createSignature(message);
      await acceptChit(wm, {
        signature,
        chit_ent: props.chit_ent,
        chit_seq: props.chit_seq,
        chit_idx: props.chit_idx,
      })

      props?.postAccept?.();

    } catch(err) {
      const { isKeyAvailable, message } = err;
      if (isKeyAvailable === false) {
        Alert.alert(
          props?.text?.nokey?.title ?? '',
          props?.text?.nokey?.help ?? '',
          [{ text: props?.text?.cancel?.title ?? '' }, { text: props?.text?.next?.title ?? '', onPress: showCreateSignatureModal }]
        );
      } else {
        showError(err);
      }
    } finally {
      setDisabled(false);
    }
  }

  return (
    <Button
      title={props.text?.approve?.title ?? 'accept_text'}
      onPress={onAccept}
      disabled={disabled}
      style={props.style ?? {}}
    />
  )
}

const styles = StyleSheet.create({
});

AcceptButton.propTypes = {
  json: PropTypes.any.isRequired,
  chit_ent: PropTypes.string.isRequired,
  chit_seq: PropTypes.number.isRequired,
  chit_idx: PropTypes.number.isRequired,
  postAccept: PropTypes.func,
}

export default AcceptButton;
