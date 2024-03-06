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
import { offerTally } from '../../services/tally';
import { setShowCreateSignatureModal } from '../../redux/profileSlice';

const OfferButton = (props) => {
  const tally = props.tally;

  const dispatch = useDispatch();
  const { wm } = useSocket();

  const [offering, setOffering] = useState(false);

  const showCreateSignatureModal = () => {
    dispatch(setShowCreateSignatureModal(true));
  }

  const onOffer = async () => {
    if(!tally?.json_core) {
      Alert.alert('Tally cannot be signed');
      return;
    }

    try {
      setOffering(true);
      const message = stringify(tally.json_core)
      const signature = await createSignature(message)
      await offerTally(wm, {
        signature,
        tally_uuid: tally.tally_uuid,
        tally_ent: tally.tally_ent,
        tally_seq: tally.tally_seq,
      })

      props?.postOffer?.();
    } catch(err) {
      const { isKeyAvailable, message } = err;
      if (isKeyAvailable === false) {
        showCreateSignatureModal();
      } else {
        Alert.alert("Error", message || err);
      }
    } finally {
      setOffering(false);
    }
  };

  return (
    <Button
      title={props.text?.offer?.title ?? 'offer_text'}
      disabled={offering}
      onPress={onOffer}
      textColor={colors.white}
      style={props.style ?? {}}
    />
  )
}

OfferButton.propTypes = {
  style: PropTypes.any,
  tally: PropTypes.object.isRequired,
  // Function to run after the offer has been made
  postOffer: PropTypes.func,
}

export default OfferButton;
