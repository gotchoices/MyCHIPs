import React, { useEffect, useState } from 'react';
import { View, StyleSheet, FlatList, ActivityIndicator } from 'react-native';

import NoActivity from './NoActivity';
import TallyItem from './TallyItem';

import { colors } from '../../config/constants';
import { fetchTallies } from '../../services/tally';
import useSocket from '../../hooks/useSocket';

const Activity = (props) => {
  const { wm } = useSocket();

  const [loading, setLoading] = useState(true);

  const [tallies, setTallies] = useState();

  useEffect(() => {
    fetchTally();
  }, []);

  const postAccept = () => {
    fetchTally();
  }

  const postOffer = () => {
    fetchTally();
  }

  const fetchTally = async () => {
    try {
      const data = await fetchTallies(wm, {
        fields: [
          'tally_ent',
          'tally_seq',
          'contract',
          'comment',
          'tally_uuid',
          'hold_terms',
          'part_terms',
          'tally_type',
          'status',
          'part_cid',
          'part_cert',
          'hold_cert',
          'json_core',
          'state',
          'crt_date',
        ],
        where: ['action true'],
      })

      setTallies(data);

    } catch(err) {
      console.log('ERR>>>', err)
    } finally {
      setLoading(false);
    }
  };

  if (loading) {
    return (
      <View style={{ flex: 1, justifyContent: "center", alignItems: "center" }}>
        <ActivityIndicator size={"large"} />
      </View>
    );
  }

  if(!loading && !tallies?.length) {
    return (
      <View style={styles.noActivity}>
        <NoActivity />
      </View>
    )
  }

  return (
    <View style={styles.main}>
      <FlatList
        data={tallies}
        keyExtractor={(item) => item.tally_uuid}
        renderItem={({ item }) => (
          <TallyItem 
            tally={item}
            navigation={props.navigation} 
            postOffer={postOffer}
            postAccept={postAccept}
          />
        )}
      />
    </View>
  );
};

const styles = StyleSheet.create({
  main: {
    flex: 1,
    paddingTop: 5,
    paddingBottom: 15,
    paddingHorizontal: 20,
  },
  item: {
    paddingVertical: 18,
    borderBottomWidth: 1,
    paddingHorizontal: 12,
    borderBottomColor: colors.lightgray,
  },
  itemLast: {
    borderBottomWidth: 0,
  },
  noActivity: {
    flex: 1,
    paddingHorizontal: '15%',
    alignItems: 'center',
    justifyContent: 'center',
  }
});

export default Activity;
