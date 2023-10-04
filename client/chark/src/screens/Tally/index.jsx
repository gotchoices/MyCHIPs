import React, { useEffect, useState, useMemo } from 'react';
import { View, StyleSheet, FlatList, TouchableWithoutFeedback } from 'react-native';
import { useSelector, useDispatch } from 'react-redux';

import useSocket from '../../hooks/useSocket';
import { round } from '../../utils/common';
import { getCurrency } from '../../services/user';
import { useUserTalliesText } from '../../hooks/useLanguage';
import { fetchOpenTallies, fetchImagesByDigest as fetchImages } from '../../redux/openTalliesSlice';

import TallyItem from './TallyItem';
import TallyHeader from './TallyHeader';

const Tally = (props) => {
  const { wm } = useSocket();
  const dispatch = useDispatch();
  const { preferredCurrency } = useSelector(state => state.profile);
  const { imageFetchTrigger, tallies: tallies, imagesByDigest, fetching } = useSelector(state => state.openTallies);
  useUserTalliesText(wm);

  const [conversionRate, setConversionRate] = useState(0);

  const currencyCode = preferredCurrency.code;

  const fetchTallies = () => {
    if(wm) {
      dispatch(fetchOpenTallies({ wm }))
    }
  }

  useEffect(() => {
    fetchTallies();
  }, [wm])

  useEffect(() => {
    if(wm) {
      dispatch(fetchImages({ wm }))
    }
  }, [wm, imageFetchTrigger])

  useEffect(() => {
    if (currencyCode) {
      getCurrency(wm, currencyCode).then(data => {
        setConversionRate(parseFloat(data?.rate ?? 0));
      }).catch(err => {
        // TODO
      })
    }
  }, [currencyCode])

  const totalNet = useMemo(() => {
    let total = tallies.reduce((acc, current) => {
      return acc + (Number(current?.net ?? 0));
    }, 0)

    return round(total / 1000, 3);
  }, [tallies])

  const totalNetDollar = useMemo(() => {
    if(conversionRate) {
      const total = totalNet * conversionRate;
      return round(total, 2);
    }

    return 0;
  }, [totalNet, conversionRate])

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
          image={imagesByDigest?.[item?.part_cert?.file?.[0]?.digest]}
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
      refreshing={fetching}
      onRefresh={fetchTallies}
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
