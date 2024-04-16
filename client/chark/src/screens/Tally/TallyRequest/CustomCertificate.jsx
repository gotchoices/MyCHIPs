import React, { useState, useEffect } from 'react';
import PropTypes from 'prop-types';
import { useSelector, useDispatch } from 'react-redux';
import Toast from 'react-native-toast-message';
import { 
  View,
  Text,
  ScrollView,
  StyleSheet,
  TouchableWithoutFeedback,
} from 'react-native';

import Header from './Header';
import Button from '../../../components/Button';
import HelpText from '../../../components/HelpText';
import BackIcon from '../../../../assets/svg/ic_back.svg';
import Spinner from '../../../components/Spinner';
import CustomCertificateSelection from '../../../components/CustomCertificateSelection';

import { colors } from '../../../config/constants';
import {
  fetchCertificate,
  setPlace,
  setBirth,
  setConnect,
  setState,
  selectAllCert,
  setFile,
} from '../../../redux/certificateTalliesSlice';
import useSocket from '../../../hooks/useSocket';
import { processTicket } from '../../../services/tally';
import useMessage from '../../../hooks/useMessageText';
import { showError } from '../../../utils/error';

const CustomCertificate = (props) => {
  const tally_ent = props.tally_ent;
  const tally_seq = props.tally_seq;
  const { fetchingSingle, certificate, place, birth, state, connect, file } = useSelector(state => state.certificateTallies);
  const { certificateChangeTrigger } = useSelector(state => state.workingTallies);
  const { userChangeTrigger } = useSelector(state => state.profile);
  const { wm } = useSocket();
  const { messageText } = useMessage();
  const charkMessageText = messageText?.chark?.msg;
  const talliesMeMessageText = messageText?.tallies_v_me?.msg;
  const { fromStartToCertSelection } = useSelector(state => state.certificateTallies)

  const [processingTicket, setProcessingTicket] = useState(false);

  const dispatch = useDispatch();

  useEffect(() => {
    // Refetch if the draft tally is changed 
    const needRefetch = (
      tally_ent && tally_seq &&
      certificateChangeTrigger?.tally_ent == tally_ent && 
      certificateChangeTrigger?.tally_seq == tally_seq &&
      certificateChangeTrigger?.trigger
    )

    if((tally_ent && tally_seq) || needRefetch) {
      dispatch(
        fetchCertificate({
          wm,
          tally_ent,
          tally_seq,
          type: 'tally',
        })
      );
    } else if(props.needCustom && userChangeTrigger/* Refetch user cert if profile change is detected */) {
      dispatch(
        fetchCertificate({
          wm,
          type: 'user',
        })
      );
    }
  }, [
    tally_ent,
    tally_seq,
    props.needCustom,
    certificateChangeTrigger?.tally_ent,
    certificateChangeTrigger?.tally_seq,
    certificateChangeTrigger?.trigger,
    userChangeTrigger,
  ])

  const onBack = () => {
    props.showCorrespondingView('certificateOptions')
  }

  const onPlaceChange = (id) => {
    return (value) => {
      dispatch(
        setPlace({ id, selected: value})
      )
    }
  }

  const onBirthChange = (selected) => {
    dispatch(
      setBirth({ selected })
    )
  }

  const onStateChange = (selected) => {
    dispatch(
      setState({ selected })
    )
  }

  const onConnectChange = (id) => {
    return (value) => {
      dispatch(
        setConnect({ id, selected: value })
      )
    }
  }

  const onFileChange = (id) => {
    return (value) => {
      dispatch(
        setFile({ id, selected: value})
      )
    }
  }

  const onSelectAll = () => {
    dispatch(
      selectAllCert()
    )
  }

  const sendCertificate = async () => {
    if(props.cert) {
      if(!certificate) {
        return Toast.show({
          type: 'error',
          text1: talliesMeMessageText?.nocert?.help ?? '',
        });
      }

      const _place = [];
      const _connect = [];
      const _file = [];
      let _state = {};
      let _birth = {};

      for(let id of place.ids) {
        const pl = place.byId[id];
        if(pl && pl.selected) {
          const { selected, ...rest } = pl;
          _place.push(rest);
        }
      }

      for(let id of connect.ids) {
        const conn = connect.byId[id];
        if(conn && conn.selected) {
          const { selected, ...rest } = conn;
          _connect.push(rest);
        }
      }

      for(let id of file.ids) {
        const fl = file.byId[id];
        if(fl && fl.selected) {
          const { selected, ...rest } = fl;
          _file.push(rest);
        }
      }

      if(state?.selected) {
        _state = state.data;
      }

      if(birth?.selected) {
        _birth = birth.data;
      }

      const part_cert = {
        ...(certificate ?? {}),
        place: _place,
        connect: _connect,
        file: _file,
        identity: {
          birth: _birth,
          state: _state,
        },
      }

      const ticketPayload = {
        ...props.cert,
        part_cert,
      }

      setProcessingTicket(true);
      try {
        await processTicket(wm, ticketPayload);
        Toast.show({
          type: 'success',
          text1: talliesMeMessageText?.requested?.title ?? ''
        });
        props.navigation.navigate('Home')
      } catch(err) {
        showError(err)
      } finally {
        setProcessingTicket(false);
      }
    }
  }

  if(fetchingSingle) {
    return (
      <View style={styles.container}>
        <Header headerText={charkMessageText?.certopts?.title}>
          <BackIcon onPress={onBack} />
        </Header>

        <View style={styles.content}>
          <Spinner />
        </View>
      </View>
    )
  }

  return (
    <View style={styles.container}>
      <ScrollView style={{ marginHorizontal: 2 }}>
        <Header headerText={charkMessageText?.certopts?.title}>
          <BackIcon onPress={onBack} />
        </Header>

        {fromStartToCertSelection && (
          <Text style={styles.headerDescription}>
            {charkMessageText?.certshare?.help}
          </Text>
        )}
        
        <View style={styles.content}>
          <TouchableWithoutFeedback
            onPress={onSelectAll}
          >
            <View style={styles.selectContainer}>
              <HelpText
                style={styles.select}
                label={charkMessageText?.selall?.title ?? ''}
              />
            </View>
          </TouchableWithoutFeedback>


          <CustomCertificateSelection
            place={place}
            chad={certificate?.chad}
            date={certificate?.date}
            birth={birth}
            state={state}
            file={file}
            connect={connect}
            onBirthChange={onBirthChange}
            onPlaceChange={onPlaceChange}
            onStateChange={onStateChange}
            onConnectChange={onConnectChange}
            onFileChange={onFileChange}
          />
        </View>

      </ScrollView>
      <View style={styles.sendCertificate}>
        <Button
          title={talliesMeMessageText?.disclose?.title ?? ''}
          onPress={sendCertificate}
          disabled={processingTicket}
        />
      </View>
    </View>
  )
}

const font = {
  fontFamily: 'inter',
  fontWeight: '500',
}

const styles = StyleSheet.create({
  container: {
    flex: 1,
  },
  content: {
    flex: 1,
    marginTop: 30,
  },
  headerDescription: {
    ...font,
    fontSize: 12,
    fontWeight: '400',
    color: colors.gray300,
    marginTop: 8,
    textAlign: 'center',
  },
  selectContainer: {
    flexDirection: 'row',
    justifyContent: 'flex-end' 
  },
  select: {
    ...font,
    color: colors.blue,
    flexDirection: 'row',
    justifyContent: 'flex-end',
    textDecorationLine: 'underline',
  },
  certificates: {
    marginTop: 10,
  },
  label: {
    ...font,
    fontSize: 14,
    color: colors.gray300,
  },
  certDetail: {
    marginBottom: 16,
  },
});

CustomCertificate.propTypes = {
  navigation: PropTypes.any,
  onDone: PropTypes.func.isRequired,
  showCorrespondingView: PropTypes.func.isRequired,
  cert: PropTypes.any.isRequired,
  needCustom: PropTypes.bool.isRequired,
  tally_ent: PropTypes.oneOfType([
    PropTypes.string,
    PropTypes.number,
  ]),
  tally_seq: PropTypes.oneOfType([
    PropTypes.string,
    PropTypes.number,
  ]),
}

export default CustomCertificate;
