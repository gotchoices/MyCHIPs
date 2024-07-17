import 'react-native-get-random-values';
import React, { useState, useMemo, useEffect } from 'react'
import { useSelector, useDispatch } from 'react-redux'
import isEqual from 'lodash.isequal';
import differenceWith from 'lodash.differencewith';
import { v4 as uuid } from 'uuid';
import { View, ScrollView, StyleSheet } from 'react-native'
import Toast from 'react-native-toast-message';

import Button from '../../../components/Button';
import DefaultCertificate from './DefaultCertificate';
import CustomCertificateSelection from '../../../components/CustomCertificateSelection';

import { colors, toastVisibilityTime } from '../../../config/constants';
import useSocket from '../../../hooks/useSocket';
import { updateHoldCert } from '../../../services/tally';
import { setCertificate, resetCertificate, setConnect, setBirth, setPlace, setState, setCertificateChangeTrigger, setFile } from '../../../redux/workingTalliesSlice';
import useMessageText from '../../../hooks/useMessageText';
import { showError } from '../../../utils/error';

const TallyCertificate = (props) => {
  const { title, cert, tally_ent, tally_seq, state: tallyState} = props.route?.params ?? {};
  const dispatch = useDispatch();
  const { wm } = useSocket();

  const [updating, setUpdating] = useState(false);
  const { personal } = useSelector(state => state.profile);
  const { place, state, birth, connect, file } = useSelector(state => state.workingTallies)

  const { messageText } = useMessageText();
  const charkMsgText = messageText?.chark?.msg;
  const talliesMessageText = messageText?.talliex_v_me?.msg;

  useEffect(() => {
    const {
      place,
      birth,
      state,
      connect,
      file,
    } = createCertificateState(personal?.cert, cert)

    dispatch(
      setCertificate({
        place,
        birth,
        state,
        connect,
        file,
      })
    )

    return () => {
      dispatch(resetCertificate());
    }
  }, [cert, personal?.cert])

  useEffect(() => {
    props.navigation.setOptions({
      title: title ?? "Tally Certificate",
    });
  }, []);

  const name = Object.values((cert?.name ?? {})).join(' ')
  const cuid = cert?.chad?.cuid ?? '';
  const agent = cert?.chad?.agent ?? '';
  const email = useMemo(() => {
    const found = (cert?.connect ?? []).find(connect => connect.media === 'email')
    return found?.address ?? ''
  }, [cert?.connect])

  const onPlaceChange = (id) => {
    return (value) => {
      dispatch(
        setPlace({ id, selected: value})
      )
    }
  }

  const onBirthChange = (selected) => {
    dispatch(
      dispatch(
        setBirth({ selected })
      )
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

  const updateCertificate = async () => {
    if(cert) {
      if(!personal?.cert) {
        return Toast.show({
          type: 'error',
          text1: talliesMessageText?.nocert?.help ?? '',
          visibilityTime: toastVisibilityTime,
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

      const hold_cert = {
        ...(personal.cert ?? {}),
        place: _place,
        connect: _connect,
        file: _file,
        identity: {
          birth: _birth,
          state: _state,
        },
      }

      setUpdating(true);
      try {
        const tally = await updateHoldCert(wm, {
          tally_ent,
          tally_seq,
          hold_cert,
        });

        // Check for CustomCertificate.jsx for the trigger changes
        dispatch(
          setCertificateChangeTrigger({
            tally_ent,
            tally_seq,
            hold_cert: tally.hold_cert,
          })
        )
        Toast.show({
          type: 'success',
          text1: charkMsgText?.updated?.help ?? '',
          visibilityTime: toastVisibilityTime,
        });
      } catch(err) {
        showError(err);
      } finally {
        setUpdating(false);
      }
    }
  }

  return (
    <ScrollView
      style={styles.container}
      contentContainerStyle={styles.contentContainer}
    >
    {tallyState === 'draft' ? (
      <View>
        <CustomCertificateSelection
          place={place}
          chad={cert?.chad}
          date={cert?.date}
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
        
      <Button
        title="Save"
        disabled={updating}
        onPress={updateCertificate}
      />
      </View>
    ): (
      <DefaultCertificate
        name={name}
        cuid={cuid}
        email={email}
        agent={agent}
      />
    )}

    </ScrollView>
  )
}


function createCertificateState(userCert, tallyCert) {
  const places = userCert?.place ?? [];
  const tallyPlaces = tallyCert?.place ?? [];

  const _birth = userCert?.identity?.birth ?? {};
  const tallyBirth = tallyCert?.identity?.birth ?? {};

  const connects = userCert?.connect ?? [];
  const tallyConnects = tallyCert?.connect ?? [];

  const _state = userCert?.identity?.state ?? {};
  const tallyState = tallyCert?.identity?.state ?? {};

  const files = userCert?.file ?? [];
  const tallyFiles = tallyCert?.file ?? [];


  const remainingPlaces = differenceWith(places, tallyPlaces, isEqual);
  const remainingConnects = differenceWith(connects, tallyConnects, isEqual);
  const remainingFiles = differenceWith(files, tallyFiles, isEqual);

  let birth = {};
  let state = {};
  const place = { byId: {}, ids: [] };
  const connect = { byId: {}, ids: [] };
  const file = { byId: {}, ids: [] };

  remainingPlaces.forEach((pl, index) => {
    const id = uuid();
    place.byId[id] = { selected: false, ...pl }
    place.ids.push(id);
  });

  tallyPlaces.forEach((pl)=> {
    const id = uuid();
    place.byId[id] = { selected: true, ...pl }
    place.ids.push(id);
  });

  tallyConnects.forEach((conn)=> {
    const id = uuid();
    connect.byId[id] = { selected: true, ...conn }
    connect.ids.push(id);
  })

  remainingConnects.forEach((conn)=> {
    const id = uuid();
    connect.byId[id] = { selected: false, ...conn }
    connect.ids.push(id);
  })

  remainingFiles.forEach((fl, index) => {
    const id = uuid();
    file.byId[id] = { selected: false, ...fl }
    file.ids.push(id);
  });

  tallyFiles.forEach((fl, index) => {
    const id = uuid();
    file.byId[id] = { selected: true, ...fl }
    file.ids.push(id);
  });

  if(_state) {
    let selected = false;
    if(tallyState && isEqual(_state, tallyState)) {
      selected = true;
    }
    state = {
      selected,
      data: _state,
    }
  }

  if(_birth) {
    let selected = false;
    if(tallyBirth && isEqual(_birth, tallyBirth)) {
      selected = true;
    }

    birth = {
      selected,
      data: _birth
    }
  }

  return {
    place,
    birth,
    connect,
    state,
    file,
  }
}

const styles = StyleSheet.create({
  container: {
    flex: 1,
    margin: 20,
  },
  detailControl: {
    marginBottom: 10,
  },
  text: {
    color: colors.black,
    fontSize: 14,
    fontFamily: 'inter',
  },
});

export default TallyCertificate;
