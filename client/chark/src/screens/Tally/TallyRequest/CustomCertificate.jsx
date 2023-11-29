import React, { useState, useEffect } from 'react';
import PropTypes from 'prop-types';
import { useSelector, useDispatch } from 'react-redux';
import Toast from 'react-native-toast-message';
import { 
  View,
  ScrollView,
  StyleSheet,
  TouchableWithoutFeedback,
} from 'react-native';

import Header from './Header';
import Button from '../../../components/Button';
import CustomCertificateItem from './CustomCertificateItem';
import HelpText from '../../../components/HelpText';
import BackIcon from '../../../../assets/svg/ic_back.svg';
import Spinner from '../../../components/Spinner';

import { colors } from '../../../config/constants';
import {
  fetchCertificate,
  setPlace,
  setBirth,
  setConnect,
  setState,
  selectAllCert,
} from '../../../redux/certificateTalliesSlice';
import useSocket from '../../../hooks/useSocket';
import { processTicket } from '../../../services/tally';

const CustomCertificate = (props) => {
  const tally_ent = props.tally_ent;
  const tally_seq = props.tally_seq;
  const { fetchingSingle, certificate, place, birth, state, connect } = useSelector(state => state.certificateTallies);
  const { tallyChangeTrigger } = useSelector(state => state.workingTallies);
  const { userChangeTrigger } = useSelector(state => state.profile);
  const { wm } = useSocket();

  const [processingTicket, setProcessingTicket] = useState(false);

  const dispatch = useDispatch();

  useEffect(() => {
    // Refetch if the draft tally is changed 
    const needRefetch = (
      tally_ent && tally_seq &&
      tallyChangeTrigger?.tally_ent == tally_ent && 
      tallyChangeTrigger?.tally_seq == tally_seq &&
      tallyChangeTrigger?.trigger
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
    tallyChangeTrigger?.tally_ent,
    tallyChangeTrigger?.tally_seq,
    tallyChangeTrigger?.trigger,
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

  const onSelectAll = () => {
    dispatch(
      selectAllCert()
    )
  }

  const sendCertificate = async () => {
    if(props.invite) {
      if(!certificate) {
        return Toast.show({
          type: 'error',
          text1: 'Certificate not found'
        });
      }

      const _place = [];
      const _connect = [];
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
        identity: {
          birth: _birth,
          state: _state,
        },
      }

      const ticketPayload = {
        ...props.invite,
        part_cert,
      }

      setProcessingTicket(true);
      try {
        await processTicket(wm, ticketPayload);
        Toast.show({
          type: 'success',
          text1: 'Tally ticket processed.'
        });
      } catch(err) {
        Toast.show({
          type: 'error',
          text1: err.message ?? 'Tally ticket process failed.'
        })
      } finally {
        setProcessingTicket(false);
      }
    }
 }

  if(fetchingSingle) {
    return (
      <View style={styles.container}>
        <Header headerText="My Custom Certificate">
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
      <ScrollView>
        <Header headerText="My Custom Certificate">
          <BackIcon onPress={onBack} />
        </Header>
        
        <View style={styles.content}>
          <TouchableWithoutFeedback
            onPress={onSelectAll}
          >
            <View style={styles.selectContainer}>
              <HelpText
                style={styles.select}
                label={'Select All'}
              />
            </View>
          </TouchableWithoutFeedback>


          {!!place.ids.length && (
            <View style={styles.certDetail}>
              <HelpText
                style={styles.label}
                label={'Place'}
              />
              
              {place.ids.map((id, index) => (
                <CustomCertificateItem 
                  key={index}
                  type="place"
                  data={place.byId[id]}
                  selected={place.byId[id]?.selected}
                  onCheckBoxChange={onPlaceChange(id)}
                />
              ))}
            </View>
          )}

          {!!birth?.data && (
            <View style={styles.certDetail}>
              <HelpText
                style={styles.label}
                label={'Birth'}
              />
              
              <CustomCertificateItem 
                type="birth"
                data={birth?.data}
                selected={birth?.selected}
                onCheckBoxChange={onBirthChange}
              />
            </View>
          )}

          {!!connect.ids.length && (
            <View style={styles.certDetail}>
              <HelpText
                style={styles.label}
                label={'Connect'}
              />
              
              {connect.ids?.map?.((id, index) => (
                <CustomCertificateItem 
                  key={index}
                  type="connect"
                  data={connect.byId[id]}
                  selected={connect.byId[id]?.selected}
                  onCheckBoxChange={onConnectChange(id)}
                />
              ))}
            </View>
          )}

          {!!state.data && (
            <View style={styles.certDetail}>
              <HelpText
                style={styles.label}
                label={'State'}
              />
              
              <CustomCertificateItem 
                type="state"
                data={state.data}
                selected={state?.selected}
                onCheckBoxChange={onStateChange}
              />
            </View>
          )}

          {!!certificate?.chad && (
            <View style={styles.certDetail}>
              <HelpText
                style={styles.label}
                label={'Chad'}
              />
              
              <CustomCertificateItem 
                type="chad"
                data={certificate.chad}
                disabled={true}
                selected={true}
              />
            </View>
          )}

          {!!certificate?.date && (
            <View style={styles.certDetail}>
              <HelpText
                style={styles.label}
                label={'Date'}
              />
              
              <CustomCertificateItem 
                type="date"
                data={{ date: certificate.date }}
                disabled={true}
                selected={true}
              />
            </View>
          )}

        </View>

      </ScrollView>
      <View style={styles.sendCertificate}>
        <Button
          title={'Send Certificate'}
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
  header: {
    flexDirection: 'row',
    justifyContent: 'center',
  },
  headerIcon: {
    position: 'absolute',
    left: 0,
    top: -3,
  },
  headerText: {
    fontFamily: 'inter',
    fontSize: 18,
    fontWeight: '500',
    color: colors.black,
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
  sendCertificate: {
    //width: '100%',
    //position: 'absolute',
    //bottom: 0,
  }
});

CustomCertificate.propTypes = {
  onDone: PropTypes.func.isRequired,
  showCorrespondingView: PropTypes.func.isRequired,
  invite: PropTypes.any.isRequired,
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
