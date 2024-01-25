import React, { useState } from 'react';
import PropTypes from 'prop-types';
import Toast from 'react-native-toast-message';

import Button from '../../../components/Button';

import useSocket from '../../../hooks/useSocket';
import { rejectChit } from '../../../services/chit';

const RejectButton = (props) => {
  const { wm } = useSocket();
  const [disabled, setDisabled] = useState(false);

  const onReject = async () => {
    setDisabled(true);
    try {
      await rejectChit(wm, {
        chit_ent: props.chit_ent,
        chit_seq: props.chit_seq,
        chit_idx: props.chit_idx,
      })

      props?.postReject?.();

      Toast.show({
        type: "success",
        text1: 'Chit has been rejected',
      });
    } catch(err) {
      Toast.show({
        type: "error",
        text1: err.message,
      });
    } finally {
      setDisabled(false);
    }
  }

  return (
    <Button
      title="Reject"
      onPress={onReject}
      disabled={disabled}
      style={props.style ?? {}}
    />
  )
}

RejectButton.propTypes = {
  chit_ent: PropTypes.string.isRequired,
  chit_seq: PropTypes.number.isRequired,
  chit_idx: PropTypes.number.isRequired,
  postReject: PropTypes.func,
}

export default RejectButton;
