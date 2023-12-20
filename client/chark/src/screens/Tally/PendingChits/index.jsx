import React, { useEffect } from 'react';
import { useSelector, useDispatch } from 'react-redux';
import {
  View,
  Text,
  FlatList,
  StyleSheet,
  TouchableWithoutFeedback,
} from 'react-native';

import Header from './Header';
import ChitItem from './ChitItem';
import HelpText from '../../../components/HelpText'

import { colors } from '../../../config/constants';
import { getChits } from '../../../redux/chitSlice';
import useSocket from '../../../hooks/useSocket';

const PendingChits = (props) => {
  const dispatch = useDispatch();
  const { wm } = useSocket();
  const { chits } = useSelector(state => state.chit)
  const { user } = useSelector((state) => state.currentUser);
  const user_ent = user?.curr_eid;
  const {  tally_uuid, partName, description, conversionRate } = props.route?.params ?? {};
  console.log(JSON.stringify(chits, null, 2), 'test')

  useEffect(() => {
    dispatch(
      getChits({
        wm,
        tally_uuid,
        chit_ent: user_ent,
      })
    )
  }, [])

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
        ListHeaderComponent={
          <HelpText
            label={'Pending Chits'}
            style={styles.listTitle}
          />
        }
        data={chits}
        renderItem={renderItem}
        showsVerticalScrollIndicator={false}
        keyExtractor={(_, index) => index}
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
