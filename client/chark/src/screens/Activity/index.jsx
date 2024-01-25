import React, { useEffect, useState } from 'react';
import { useSelector, useDispatch } from 'react-redux';
import { View, StyleSheet, FlatList, ActivityIndicator } from 'react-native';

import NoActivity from './NoActivity';
import TallyItem from './TallyItem';
import ChitItem from '../Tally/PendingChits/ChitItem';

import { colors } from '../../config/constants';
import useSocket from '../../hooks/useSocket';
import { getChits, getTallies } from '../../redux/activitySlice';

const Activity = (props) => {
  const { wm, chitTrigger, tallyNegotiation } = useSocket();
  const dispatch = useDispatch();

  const { tallies, chits, fetchingTallies, fetchingChits } = useSelector(state => state.activity)
  const activities = [...tallies, ...chits];

  useEffect(() => {
    fetchChits();
  }, [chitTrigger])

  useEffect(() => {
    fetchTallies();
  }, [tallyNegotiation])

  const fetchTallies = async () => {
    dispatch(getTallies({ wm }))
  };

  const fetchChits = async () => {
    dispatch(getChits({ wm }))
  };

  const postTallyAccept = () => {
    fetchTallies();
  }

  const postTallyOffer = () => {
    fetchTallies();
  }

  const postChitAccept = () => {
    fetchChits();
  }

  const postChitReject = () => {
    fetchChits();
  }

  const renderItem = ({ item }) => {
    if(item.tally_ent) {
      return (
        <TallyItem 
          tally={item}
          navigation={props.navigation} 
          postOffer={postTallyOffer}
          postAccept={postTallyAccept}
        />
      )
    } else if(item.chit_ent) {
      return (
        <ChitItem
          chit={item}
          navigation={props.navigation} 
          conversionRate={0}
          avatar={'test'}
          postAccept={postChitAccept}
          postReject={postChitReject}
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

  if(!fetchingTallies && !activities?.length) {
    return (
      <View style={styles.noActivity}>
        <NoActivity />
      </View>
    )
  }

  return (
    <View style={styles.main}>
      <FlatList
        data={activities}
        keyExtractor={(item) => item.tally_uuid ?? item.chit_uuid}
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
