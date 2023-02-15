import React, { useEffect, useCallback } from 'react';
import {
  View,
  Text,
  Linking,
} from 'react-native';
import { useFocusEffect } from '@react-navigation/native';

import { parse } from '../../utils/query-string';
import { getLinkHost } from '../../utils/common';

const tallyUri = new Set(['tally-accept', 'mychips.org/tally-accept']);
const TallyAccept = (props) => {
  useEffect(() => {
    Linking.getInitialURL().then((url) => {
      const host = getLinkHost(url ?? '');
      if(!tallyUri.has(host)) {
        return;
      }

      const obj = parse(url);
      console.log(obj)
    });

  }, []);

  useFocusEffect(
    useCallback(() => {
      const listener = Linking.addEventListener('url', ({url}) => {
        const host = getLinkHost(url ?? '');
        if(!tallyUri.has(host)) {
          return;
        }

        const obj = parse(url);
        console.log(obj)
      })

      return () => {
        listener.remove();
      };
    }, [])
  );

  return (
    <View>
      <Text>Tally accept</Text>
    </View>
  )
}

export default TallyAccept;
