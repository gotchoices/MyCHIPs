import React, { useState, useEffect, useMemo } from 'react';
import { useSelector, useDispatch } from 'react-redux';
import { View, StyleSheet, FlatList, ActivityIndicator } from 'react-native';

import NoActivity from './NoActivity';
import TallyItem from './TallyItem';
import ChitItem from '../Tally/PendingChits/ChitItem';

import { colors } from '../../config/constants';
import useSocket from '../../hooks/useSocket';
import { useChitsMeText } from '../../hooks/useLanguage';
import { getCurrency } from '../../services/user';
import { getChits, getTallies, setHasNotification, getGoodChits } from '../../redux/activitySlice';

const Activity = (props) => {
  const { wm, chitTrigger, tallyNegotiation } = useSocket();
  const dispatch = useDispatch();

  const [conversionRate, setConversionRate] = useState(0);

  const { preferredCurrency } = useSelector((state) => state.profile);

  const currencyCode = preferredCurrency.code;
  const { tallies = [], chits = [], fetchingTallies, fetchingChits, goodChits = [] } = useSelector(state => state.activity)
  const activities = useMemo(() => {
    return [...tallies, ...chits];
  }, [tallies, chits])

  const allActivities = useMemo(() => {
    return [...activities, ...goodChits]
  }, [activities, goodChits])

  // Register chits texts
  useChitsMeText(wm);

  useEffect(() => {
    fetchChits();
  }, [chitTrigger])

  useEffect(() => {
    fetchTallies();
  }, [tallyNegotiation])

  useEffect(() => {
    dispatch(getGoodChits({ wm }));
  }, [chitTrigger])

  useEffect(() => {
    // Setting only after the tallies and chits have been fetched
    if(!fetchingChits && !fetchingTallies) {
      dispatch(setHasNotification(!!activities.length))
    }
  }, [activities?.length])

  useEffect(() => {
    if (currencyCode) {
      getCurrency(wm, currencyCode)
        .then((data) => {
          setConversionRate(parseFloat(data?.rate ?? 0));
        })
        .catch((err) => {
          console.log("EXCEPTION ==> ", err);
        })
    }
  }, [currencyCode]);

  const fetchTallies = async () => {
    dispatch(getTallies({ wm }))
  };

  const fetchChits = async () => {
    dispatch(getChits({ wm }))
  };

  const postTallyAction = () => {
    fetchTallies();
  }

  const postChitAction = () => {
    fetchChits();
  }

  const renderItem = ({ item }) => {
    if(item.tally_ent) {
      return (
        <TallyItem 
          tally={item}
          navigation={props.navigation} 
          postOffer={postTallyAction}
          postAccept={postTallyAction}
        />
      )
    } else if(item.chit_ent) {
      return (
        <ChitItem
          chit={item}
          navigation={props.navigation} 
          conversionRate={conversionRate}
          avatar={'test'}
          postAccept={postChitAction}
          postReject={postChitAction}
        />
      )
    }
  }

  //if (fetchingTallies) {
    //return (
      //<View style={{ flex: 1, justifyContent: "center", alignItems: "center" }}>
        //<ActivityIndicator size={"large"} />
      //</View>
    //);
  //}

  if(!fetchingTallies && !allActivities?.length) {
    return (
      <View style={styles.noActivity}>
        <NoActivity />
      </View>
    )
  }

  return (
    <View style={styles.main}>
      <FlatList
        data={allActivities}
        keyExtractor={(item) => item.chit_uuid ?? item.tally_uuid}
        renderItem={renderItem}
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
