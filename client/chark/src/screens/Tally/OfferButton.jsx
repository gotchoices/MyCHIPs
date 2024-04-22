import React, { useState } from 'react';
import { useDispatch  } from 'react-redux';
import PropTypes from 'prop-types';
import stringify from 'json-stable-stringify';
import {
  Alert,
} from 'react-native';
import Toast from 'react-native-toast-message';

import Button from '../../components/Button';

import useSocket from '../../hooks/useSocket';
import { colors, toastVisibilityTime } from '../../config/constants';
import { createSignature } from '../../utils/message-signature';
import { offerTally } from '../../services/tally';
import { setShowCreateSignatureModal } from '../../redux/profileSlice';
import { showError } from '../../utils/error';
import { KeyNotFoundError } from '../../utils/Errors';
import { comparePublicKey } from '../../services/tally';

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

      const tallyType = tally?.tally_type;
      const tallyPublicKey = tally?.json_core?.[tallyType]?.cert?.public;
      const isNewPublicKey = await comparePublicKey(tallyPublicKey)

      if(!isNewPublicKey) {
        return Toast.show({
          type: 'success',
          text1: 'New key cannot used for signing the tally',
          visibilityTime: toastVisibilityTime,
        })
      }

      const signature = await createSignature(message)
      await offerTally(wm, {
        signature,
        tally_uuid: tally.tally_uuid,
        tally_ent: tally.tally_ent,
        tally_seq: tally.tally_seq,
      })

      props?.postOffer?.();
    } catch(err) {
      if(err instanceof KeyNotFoundError) {
        showCreateSignatureModal();
      } else {
        showError(err);
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
