import React, { useEffect } from 'react';
import moment from 'moment';
import PropTypes from 'prop-types';
import { useSelector, useDispatch } from 'react-redux';
import {
  View,
  Text,
  FlatList,
  StyleSheet,
  RefreshControl,
  TouchableWithoutFeedback,
} from 'react-native';

import Search from '../Search'
import KeyIcon from '../../../../assets/svg/ic_key.svg';
import FilterIcon from '../../../../assets/svg/ic_filter.svg';

import useSocket from "../../../hooks/useSocket";
import { colors } from '../../../config/constants';
import { fetchTalliesForCertificates } from '../../../redux/certificateTalliesSlice';

const ListItem = (props) => {
  return (
    <TouchableWithoutFeedback
      onPress={props.onPress}
    >
      <View style={styles.item}>
        <View>
          <Text style={styles.itemName}>
            {props.name}
          </Text>

          <Text style={styles.itemDate}>
            Created {props.createdAt ? moment(props.createdAt).format('DD/MM/YYYY') : 'N/A'}
          </Text>
        </View>
        <KeyIcon />
      </View>
    </TouchableWithoutFeedback>
  )
}

const Certificates = (props) => {
  const dispatch = useDispatch();
  const { tallies, fetching } = useSelector(state => state.certificateTallies)

  const { wm } = useSocket();

  const getCertificates = () => {
    dispatch(
      fetchTalliesForCertificates({ wm })
    );
  }

  useEffect(() => {
    getCertificates();
  }, [wm, fetchTalliesForCertificates, dispatch])

  return (
    <View>
      <View style={styles.header}>
        <Text style={styles.headerMain}>
          Your Certificate Options
        </Text>

        <Text style={styles.headerDescription}>
          What information will you share?
        </Text>
      </View>

      <View style={styles.content}>
        <View>
          <View style={styles.section1}>
            <Text>
              Certificates From Tally Templates
            </Text>
            
            <TouchableWithoutFeedback
              onPress={props.onCustomPressed}
            >
              <View style={styles.filter}>
                <FilterIcon />
                <Text style={{ marginLeft: 5, colors: colors.gray300 }}>Custom</Text>
              </View>
            </TouchableWithoutFeedback>
          </View>

          <Search />

          <FlatList
            data={tallies}
            keyExtractor={(item) => `${item.tally_ent}-${item.tally_seq}`}
            refreshControl={
              <RefreshControl
                refreshing={fetching}
                onRefresh={getCertificates}
              />
            }
            renderItem={({ item,index }) => {
              return (
                <ListItem
                  onPress={() => props.onItemPressed(item.tally_ent, item.tally_seq)}
                  name={item.comment ?? 'Draft'}
                  createdAt={item.crt_date}
                />
              );
            }}
          />

        </View>
      </View>
    </View>
  )
}

const font = {
  fontFamily: 'inter',
  fontWeight: '500',
}

const styles = StyleSheet.create({
  container: {},
  header: {
    alignItems: 'center',
    marginBottom: 50
  },
  headerMain: {
    ...font,
    fontSize: 18,
    color: colors.gray300,
    marginBottom: 8,
  },
  headerDescription: {
    ...font,
    fontSize: 12,
    fontWeight: '400',
    color: colors.gray300,
  },
  section1: {
    marginBottom: 10,
    flexDirection: 'row',
    justifyContent: 'space-between',
  },
  filter: {
    paddingHorizontal: 10,
    paddingVertical: 3,
    borderRadius: 13,
    flexDirection: 'row',
    alignItems: 'center',
    backgroundColor: colors.white100,
  },
  item: {
    flexDirection: 'row',
    alignItems: 'center',
    justifyContent: 'space-between',
    borderBottomColor: colors.lightgray,
    borderBottomWidth: 0.5,
    paddingVertical: 12,
  },
  itemName: {
    ...font,
    color: colors.black,
    fontSize: 16,
    fontWeight: '400'
  },
  itemDate: {
    ...font,
    fontWeight: '400',
    color: colors.gray300,
  }
})

Certificates.propTypes = {
  onCustomPressed: PropTypes.func.isRequired,
  onItemPressed: PropTypes.func.isRequired,
}

export default Certificates;
