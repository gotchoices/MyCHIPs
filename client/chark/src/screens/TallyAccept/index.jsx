import React, { useEffect, useCallback, useState } from 'react';
import {
  View,
  Text,
  Linking,
} from 'react-native';
import { useFocusEffect } from '@react-navigation/native';

import { parse } from '../../utils/query-string';
import { getLinkHost } from '../../utils/common';

const tallyUri = new Set(['tally', 'mychips.org/tally']);
const TallyAccept = (props) => {
  const { ticket } = props.route?.params ?? {};
  const [tally, setTally] = useState(ticket);

  useEffect(() => {
    if(!ticket) {
      Linking.getInitialURL().then((url) => {
        const host = getLinkHost(url ?? '');
        if(!tallyUri.has(host)) {
          return;
        }

        const obj = parse(url);
        console.log(obj);
      });

    }
  }, []);

  useFocusEffect(
    useCallback(() => {
      if(!ticket) {
        const listener = Linking.addEventListener('url', ({url}) => {
          const host = getLinkHost(url ?? '');
          if(!tallyUri.has(host)) {
            return;
          }

          const obj = parse(url);
          console.log(obj, typeof obj.chad);
        })

        return () => {
          listener.remove();
        };
      }
    }, [])
  );

  return (
    <View>
      <Text>Tally accept</Text>
    </View>
  )
}

export default TallyAccept;
