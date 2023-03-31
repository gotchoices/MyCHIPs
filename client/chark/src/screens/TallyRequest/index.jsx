import React, { useEffect, useCallback, useState } from 'react';
import {
  View,
  Text,
  Linking,
  StyleSheet,
  TextInput,
  ScrollView,
} from 'react-native';
import qs from 'query-string';
import { Picker } from '@react-native-picker/picker';
import { useFocusEffect } from '@react-navigation/native';

import { parse } from '../../utils/query-string';
import { getLinkHost } from '../../utils/common';
import { colors } from '../../config/constants';
import useSocket from '../../hooks/useSocket';

import Button from '../../components/Button';
import CustomText from '../../components/CustomText';
import CommonTallyView from '../Tally/CommonTallyView';

const tallyUri = new Set(['tally', 'mychips.org/tally']);

const TallyRequest = (props) => {
  const { ticket } = props.route?.params ?? {};
  const { wm } = useSocket();

  const [processing, setProcessing] = useState('Processing ticket...');

  // TODO: Maybe handle the url from single file 
  useEffect(() => {
    if(!ticket) {
      Linking.getInitialURL().then((url) => {
        const host = getLinkHost(url ?? '');
        console.log('mounted host', url, host)
        if(!tallyUri.has(host)) {
          return;
        }

        const parsed = parseTallyInvitation(url);
        requestProposedTally(ticket)
      });
    } else {
      requestProposedTally(ticket)
    }
  }, []);

  useFocusEffect(
    useCallback(() => {
      if(!ticket) {
        const listener = Linking.addEventListener('url', ({ url }) => {
          const host = getLinkHost(url ?? '');
          if(!tallyUri.has(host)) {
            return;
          }

          const parsed = parseTallyInvitation(url);
          console.log('focus mounted', parsed)
          requestProposedTally(parsed);
        })

        return () => {
          listener.remove();
        };
      }
    }, [])
  );

  function requestProposedTally(ticket) {
    const spec = {
      view: 'mychips.ticket_process',
      params: [ticket],
    }

    wm.request('_process_tally', 'select', spec, (data, err) => {
      if(err) {
        setProcessing(err?.message ?? 'Error processing ticket');
      } else if(data?.[0]?.ticket_process) {
        setProcessing('Ticket processed');
      } else {
        setProcessing('Ticket process failed');
      }

    });
  }

  return (
    <View style={styles.container}>
        <Text>{processing}</Text>
    </View>
  )
}

function parseTallyInvitation(url) {
  const parsed = qs.parseUrl(url);
  const query = parsed.query;

  const token = query.token;

  if(query.chad) {
    try {
      const chad = JSON.parse(query.chad);

      return {
        token,
        chad,
      }
    } catch{
      return;
    }
  }
}

const styles = StyleSheet.create({
  container: {
    flex: 1,
    margin: 10,
    padding: 10,
    backgroundColor: colors.white,
  },
}) 

export default TallyRequest;
