import React, { useEffect, useState, useMemo } from 'react';
import { View, StyleSheet, FlatList, TouchableWithoutFeedback, Text } from 'react-native';

import useSocket from '../../hooks/useSocket';
import useProfile from '../../hooks/useProfile';
import { round } from '../../utils/common';
import useCurrentUser from '../../hooks/useCurrentUser';;
import { fetchTallies } from '../../services/tally';
import { getCurrency } from '../../services/user';

import TallyItem from './TallyItem';
import TallyHeader from './TallyHeader';

const Tally = (props) => {
  const { wm, ws } = useSocket();
  const { user } = useCurrentUser();
  const { preferredCurrency } = useProfile();

  const [loading, setLoading] = useState(false);
  const [tallies, setTallies] = useState([]);
  const [conversionRate, setConversionRate] = useState(0);

  const currencyCode = preferredCurrency.code;

  useEffect(() => {
    if (currencyCode) {
      getCurrency(wm, currencyCode).then(data => {
        setConversionRate(parseFloat(data?.rate ?? 0));
      }).catch(err => {
        // TODO
      })
    }
  }, [currencyCode])

  useEffect(() => {
    if (ws) {
      _fetchTallies()
    }
  }, [ws, user?.curr_eid])

  const totalNet = useMemo(() => {
    let total = tallies.reduce((acc, current) => {
      return acc + (Number(current?.net ?? 0));
    }, 0)

    return round(total / 1000, 2);
  }, [tallies])

  const totalNetDollar = useMemo(() => {
    if(conversionRate) {
      const total = totalNet * conversionRate;
      return round(total, 2);
    }

    return 0;
  }, [totalNet, conversionRate])


  const _fetchTallies = () => {
    setLoading(true);
    fetchTallies(wm, {
      fields: ['tally_seq', 'tally_ent', 'net', 'tally_type', 'part_chad', 'part_cert'],
      where: {
        status: 'open',
      }
    }).then(data => {
      if (data) {
        setTallies(data);
      }
    }).catch(err => {
      console.log('Error fetching tallies', err)
    }).finally(() => {
      setLoading(false);
    })
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
        <TallyItem
          tally={item}
          conversionRate={conversionRate} 
          currency={preferredCurrency?.code}
        />
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
          navigation={props.navigation}
        />
      }
      contentContainerStyle={styles.contentContainer}
      data={tallies}
      renderItem={renderItem}
      showsVerticalScrollIndicator={false}
      keyExtractor={(_, index) => index}
      refreshing={loading}
      onRefresh={_fetchTallies}
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
