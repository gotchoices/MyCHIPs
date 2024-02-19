import React, { useEffect } from 'react';
import { useSelector, useDispatch } from 'react-redux';
import {
  View,
  Text,
  FlatList,
  StyleSheet,
  RefreshControl,
  TouchableWithoutFeedback,
} from 'react-native';

import Header from './Header';
import ChitItem from './ChitItem';
import HelpText from '../../../components/HelpText'

import { colors } from '../../../config/constants';
import { getChits } from '../../../redux/chitSlice';
import useSocket from '../../../hooks/useSocket';
import { useChitsMeText } from '../../../hooks/useLanguage';

const PendingChits = (props) => {
  const dispatch = useDispatch();
  const { wm, chitTrigger } = useSocket();
  const { fetching, chits } = useSelector(state => state.chit)
  const { tally_uuid, partName, description, conversionRate } = props.route?.params ?? {};

  // Register chits texts
  const chitsMeText = useChitsMeText(wm);
  const chitsMeMessageText = chitsMeText?.msg;

  const fetchChits = () => {
    dispatch(
      getChits({
        wm,
        tally_uuid,
      })
    )
  }

  useEffect(() => {
    fetchChits();
  }, [dispatch, getChits, wm, tally_uuid, chitTrigger])

  const onBack = () => {
    props.navigation.navigate('Home')
  }

  const renderItem = ({ item, index }) => (
    <TouchableWithoutFeedback onPress={()=>{}}>
      <View>
        <ChitItem
          chit={item}
          navigation={props.navigation}
          conversionRate={conversionRate}
        />
      </View>
    </TouchableWithoutFeedback>
  );

  return (
    <View style={styles.container}>
      <View style={{ marginBottom: 28 }}>
        <Header onBackPress={onBack}>
          <Text style={styles.name}>
            {partName}
          </Text>

          <Text style={styles.cid}>
            {description}
          </Text>
        </Header>
      </View>

      <FlatList
        data={chits}
        renderItem={renderItem}
        showsVerticalScrollIndicator={false}
        keyExtractor={(_, index) => index}
        ListHeaderComponent={
          <HelpText
            label={chitsMeMessageText?.pending?.title ?? ''}
            helpText={chitsMeMessageText?.pending?.help ?? ''}
            style={styles.listTitle}
          />
        }
        refreshControl={
          <RefreshControl
            refreshing={fetching}
            onRefresh={fetchChits}
          />
        }
      />
    </View>
  )
}

const font = {
  fontFamily: 'inter',
  fontWeight: '500',
}

const styles = StyleSheet.create({
  container: {
    marginHorizontal: 24,
  },
  listTitle: {
    ...font,
    fontSize: 16,
    width: '100%',
    borderBottomWidth: 0.5,
    borderBottomColor: colors.gray300,
  },
  name: {
    fontSize: 25,
    fontWeight: '400',
    fontFamily: 'inter',
    color: colors.black,
  },
  cid: {
    fontSize: 16,
    fontFamily: 'inter',
    fontWeight: '500',
    color: colors.gray300,
  }
});

export default PendingChits;
