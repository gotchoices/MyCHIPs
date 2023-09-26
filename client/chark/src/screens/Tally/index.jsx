import React, { useEffect, useState, useMemo } from 'react';
import { View, StyleSheet, FlatList, TouchableWithoutFeedback } from 'react-native';
import { Buffer } from 'buffer';
import AsyncStorage from '@react-native-async-storage/async-storage'
import { useSelector } from 'react-redux';

import useSocket from '../../hooks/useSocket';
import { round } from '../../utils/common';
import { fetchTallies, fetchTallyFile } from '../../services/tally';
import { getCurrency } from '../../services/user';
import { useUserTalliesText } from '../../hooks/useLanguage';
import { localStorage } from '../../config/constants';

import TallyItem from './TallyItem';
import TallyHeader from './TallyHeader';

const Tally = (props) => {
  const { wm, ws } = useSocket();
  const { user } = useSelector(state => state.currentUser);
  const { preferredCurrency } = useSelector(state => state.profile);
  useUserTalliesText(wm);

  const [loading, setLoading] = useState(false);
  const [tallies, setTallies] = useState([]);
  const [conversionRate, setConversionRate] = useState(0);
  const [imagesByDigest, setImagesByDigest] = useState({})  // will be as {[digest]: 'base64'}

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

    return round(total / 1000, 3);
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

        const hashes = [];
        for(let tally of data) {
          const digest = tally?.part_cert?.file?.[0]?.digest;
          const tally_seq = tally?.tally_seq;

          if(digest) {
            hashes.push({
              tally_seq,
              digest,
            });
          }
        }

        // Fetch images by digest
        fetchImagesByDigest(wm, hashes, setImagesByDigest).catch(console.log)
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
          image={imagesByDigest[item?.part_cert?.file?.[0]?.digest]}
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

async function fetchImagesByDigest(wm, hashes, setImagesByDigest) {
  const promises = [];

  let imagesByDigest = {};
  try {
    const storageValue = await AsyncStorage.getItem(localStorage.TallyPictures);
    imagesByDigest = JSON.parse(storageValue ?? {});
  } catch(err) {
    imagesByDigest = {};
  }

  for(let hash of hashes) {
    if(hash.digest in imagesByDigest) {
      continue;
    }

    promises.push(fetchTallyFile(wm, hash.digest, hash.tally_seq));
  }

  try {
    const files = await Promise.all(promises);

    for(let file of files) {
      const fileData = file?.[0]?.file_data;
      const file_fmt = file?.[0]?.file_fmt;
      const digest = file?.[0]?.digest;

      if(fileData) {
        const base64 = Buffer.from(fileData).toString('base64')
        const image = `data:${file_fmt};base64,${base64}`;
        imagesByDigest[digest] = image;
      }
    }

    await AsyncStorage.setItem(localStorage.TallyPictures, JSON.stringify(imagesByDigest));

    setImagesByDigest(prev => {
      return {
        ...prev,
        ...imagesByDigest
      }
    })
  } catch(err) {
    throw err;
  }
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
