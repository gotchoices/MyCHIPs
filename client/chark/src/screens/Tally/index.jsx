import React, { useEffect, useState, useMemo } from 'react';
import { View, StyleSheet, FlatList, TouchableWithoutFeedback } from 'react-native';

import constants from '../../config/constants';
import { round} from '../../utils/common';
import Banner from './Banner';
import Search from './Search';
import TallyItem from './TallyItem';
let pktId = 1;

const Tally = (props) => {
  const wm = props.wm;
  const [loading, setLoading] = useState(true);
  const [tallies, setTallies] = useState([]);
  const [currentUser, setCurrentUser] = useState('');

  const totalNet = useMemo(() => {
    let total = tallies.reduce((acc, current) => {
      return acc + (Number(current?.net ?? 0));
    }, 0)

    return round(total / 1000, 2);
  }, [tallies])

  const totalNetDollar = useMemo(() => {
    const total = totalNet * constants.chipsToDollar;
    return round(total, 2);
  }, [totalNet])

  useEffect(() => {
    fetchCurrentUser();
    fetchTallies()
  }, [])

  const fetchCurrentUser = () => {
    props.wm.request(pktId++, 'select', {
      view: 'base.ent_v',
      table: 'base.curr_eid',
      params: []
    }, data => {
      setCurrentUser(data?.[0]?.curr_eid);
    })
  }

  const fetchTallies = () => {
    const spec = {
      fields: ['tally_seq', 'tally_ent', 'net', 'tally_type', 'part_chad', 'part_cert'],
      view: 'mychips.tallies_v_me',
      where: {
        status: 'open',
      }
    }

    wm.request('_inv_ref', 'select', spec, data => {
      if(data) {
        setTallies(data);
        setLoading(false);
      }
    });
  }

  const onItemPress = ({ tally_seq, tally_ent }) => {
    return () => {
      props.navigation.navigate('OpenTallyEdit', {
        tally_seq,
        tally_ent,
      });
    }
  }

  const renderItem = ({ item, index }) => (
    <TouchableWithoutFeedback 
      onPress={onItemPress({
        tally_seq: item.tally_seq,
        tally_ent: item.tally_ent,
      })}
    >
      <View style={[styles.item, index === tallies?.length - 1 ? styles.itemLast : null]}>
        <TallyItem tally={item} />
      </View>
    </TouchableWithoutFeedback>
  );

  return (
    <View style={styles.container}>
      <Banner 
        totalNet={totalNet}
        totalNetDollar={totalNetDollar}
        navigation={props.navigation}
        user={currentUser}
      /> 

      <View style={styles.search}>
        <Search />
      </View>

      <View style={styles.listContainer}>
        <FlatList
          data={tallies}
          renderItem={renderItem}
          showsVerticalScrollIndicator={false}
          keyExtractor={(item, index) => index}
          refreshing={loading}
          onRefresh={() => fetchTallies()}
        />

      </View>
    </View>
  )
}

const styles = StyleSheet.create({
  container: {
    flex: 1,
  },
  search: {
    marginTop: 16,
    backgroundColor: '#fff',
    paddingHorizontal: 24,
    paddingVertical: 16,
  },
  listContainer: {
    flex: 1,
    backgroundColor: '#fff',
    width: '90%',
    paddingVertical: 10,
    paddingHorizontal: 16,
    borderRadius: 8,
    alignSelf: 'center',
    marginTop: 32,
    marginBottom: 55,
  },
  item: {
    paddingVertical: 18,
    borderBottomWidth: 2,
    borderBottomColor: '#E4E7EC',
  },
  itemLast: {
    borderBottomWidth: 0,
  }
});


export default Tally;
