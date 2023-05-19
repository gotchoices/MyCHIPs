import React, { useEffect, useState, useMemo, useCallback } from 'react';
import { View, StyleSheet, FlatList, TouchableWithoutFeedback, Text } from 'react-native';

import useSocket from '../../hooks/useSocket';
import useProfile from '../../hooks/useProfile';
import constants from '../../config/constants';
import { round } from '../../utils/common';
import useCurrentUser from '../../hooks/useCurrentUser';;

import Banner from './Banner';
import Search from './Search';
import TallyItem from './TallyItem';
import TallyHeader from './TallyHeader';
import { random } from '../../utils/common';

const Tally = (props) => {
  const [loading, setLoading] = useState(false);
  const [tallies, setTallies] = useState([]);
  const { wm, ws } = useSocket();
  const { user } = useCurrentUser();
  const { preferredCurrency } = useProfile();
  const currencyCode = preferredCurrency.code;

  const [fiatRate, setFiatRate] = useState(0);
  const totalNet = useMemo(() => {
    let total = tallies.reduce((acc, current) => {
      return acc + (Number(current?.net ?? 0));
    }, 0)

    return round(total / 1000, 2);
  }, [tallies])

  const totalNetDollar = useMemo(() => {
    const total = totalNet * fiatRate ?? constants.chipsToDollar;
    return round(total, 2);
  }, [totalNet, fiatRate])

  useEffect(() => {
    if (currencyCode) {
      const espec = {
        name: 'chip',
        view: 'mychips.users_v_me',
        data: {
          options: {
            curr: currencyCode,
            format: 'json'
          }
        }
      };

      wm.request(`chip_json_${random(1000)}`, 'action', espec, (data, err) => {
        setFiatRate(data?.fiat_rate);
      });
    }
  }, [currencyCode])

  useEffect(() => {
    if (ws) {
      fetchTallies()
    }
  }, [user?.curr_eid])

  const fetchTallies = () => {
    setLoading(true);
    const spec = {
      fields: ['tally_seq', 'tally_ent', 'net', 'tally_type', 'part_chad', 'part_cert'],
      view: 'mychips.tallies_v_me',
      where: {
        status: 'open',
      }
    }

    wm.request('_inv_ref', 'select', spec, data => {
      if (data) {
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
    <FlatList
      ListHeaderComponent={
        <TallyHeader
          totalNet={totalNet}
          totalNetDollar={totalNetDollar}
          currencyCode={preferredCurrency.code}
        />
      }
      contentContainerStyle={styles.contentContainer}
      data={tallies}
      renderItem={renderItem}
      showsVerticalScrollIndicator={false}
      keyExtractor={(_, index) => index}
      refreshing={loading}
      onRefresh={() => fetchTallies()}
    />
  )
}

const styles = StyleSheet.create({
  contentContainer: {
    paddingBottom: 16,
  },
  item: {
    paddingVertical: 18,
    borderBottomWidth: 2,
    borderBottomColor: '#E4E7EC',
    width: "90%",
    alignSelf: 'center',
    paddingHorizontal: 12,
    backgroundColor: '#FFFFFF'
  },
  itemLast: {
    borderBottomWidth: 0,
  }
});


export default Tally;
