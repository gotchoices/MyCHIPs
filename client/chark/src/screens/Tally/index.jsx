import React, {useEffect, useState, useMemo} from 'react';
import {
  View,
  StyleSheet,
  FlatList,
  TouchableWithoutFeedback,
  Text,
} from 'react-native';
import {useSelector, useDispatch} from 'react-redux';

import useSocket from '../../hooks/useSocket';
import {round, unitsToChips, formatChipValue, unitsToFormattedChips} from '../../utils/common';
import {getCurrency} from '../../services/user';
import {useTalliesMeText, useChitsMeText} from '../../hooks/useLanguage';
import {
  fetchOpenTallies,
  updateTallyOnChitTransferred,
} from '../../redux/openTalliesSlice';
import {fetchImagesByDigest as fetchImages} from '../../redux/avatarSlice';

import TallyItem from './TallyItem';
import TallyHeader from './TallyHeader';
import PayModal from '../Pay';
import {colors} from '../../config/constants';
import {
  getTallyName,
  sortTallies,
  sortTalliesAlphabetically,
} from '../../utils/user';

const connectionStatus = {
  connected: 'Connected',
  disconnect: 'Disconnected',
  connecting: 'Connecting',
};

const Tally = props => {
  const {wm, tallyNegotiation, chitTrigger, status} = useSocket();
  const dispatch = useDispatch();
  const {preferredCurrency, filterTally} = useSelector(state => state.profile);
  const {
    imageFetchTrigger,
    tallies: tallies,
    /*imagesByDigest,*/ fetching,
  } = useSelector(state => state.openTallies);
  const {imagesByDigest} = useSelector(state => state.avatar);
  useTalliesMeText(wm);
  useChitsMeText(wm);

  const [conversionRate, setConversionRate] = useState(0);

  const currencyCode = preferredCurrency.code;

  const [tally, setTally] = useState();

  const [isVisible, setIsVisible] = useState(false);

  const [sortedTallies, setSortedTallies] = useState(tallies);

  const [filteredTallies, setFilteredTallies] = useState(sortedTallies);

  const onSearch = text => {
    if (text.length >= 2) {
      const newTallies = sortedTallies.filter(tally => {
        const partName = getTallyName(tally);
        const cuid = tally.part_cert?.chad?.cuid;

        return (
          partName.toLowerCase().includes(text.toLowerCase()) ||
          cuid.toLowerCase().includes(text.toLowerCase())
        );
      });

      if (newTallies) {
        return setFilteredTallies(newTallies);
      }
    }

    return fetchFilteredTallies();
  };

  const getTalliesAlphabetically = () => {
    const sortedArray = sortTalliesAlphabetically(tallies);

    setSortedTallies(sortedArray);
    setFilteredTallies(sortedArray);
  };

  const getSortedTallies = (field, descending) => {
    const sortedArray = sortTallies(tallies, field, descending);

    setSortedTallies(sortedArray);
    setFilteredTallies(sortedArray);
  };

  const fetchFilteredTallies = () => {
    if (wm) {
      const selectedKey = Object.keys(filterTally).find(
        key => filterTally[key].selected === true,
      );

      switch (selectedKey) {
        case 'absolute':
          return getSortedTallies('mag_p', true);

        case 'ascending':
          return getSortedTallies('net', true);

        case 'descending':
          return getSortedTallies('net', false);

        case 'recent':
          return getSortedTallies('tally_date', true);

        case 'alphabetical':
          return getTalliesAlphabetically();

        default:
          return getSortedTallies('tally_date', true);
      }
    }
  };

  useEffect(() => {
    if (tallies) {
      fetchFilteredTallies();
    }
  }, [tallies]);

  useEffect(() => {
    fetchFilteredTallies();
  }, [filterTally]);

  const fetchTallies = () => {
    if (wm) {
      dispatch(fetchOpenTallies({wm}));
    }
  };

  useEffect(() => {
    fetchTallies();
  }, [wm, dispatch, fetchOpenTallies, tallyNegotiation]);

  useEffect(() => {
    if (wm) {
      dispatch(fetchImages({wm, status: 'open'}));
    }
  }, [wm, imageFetchTrigger]);

  useEffect(() => {
    if (currencyCode) {
      getCurrency(wm, currencyCode)
        .then(data => {
          setConversionRate(parseFloat(data?.rate ?? 0));
        })
        .catch(err => {
          // TODO
        });
    }
  }, [currencyCode]);

  useEffect(() => {
    if (chitTrigger) {
      dispatch(updateTallyOnChitTransferred(chitTrigger));
    }
  }, [chitTrigger]);

  // Calculate total units
  const totalNetUnits = useMemo(() => {
    return tallies.reduce((acc, current) => {
      return acc + Number(current?.net ?? 0);
    }, 0);
  }, [tallies]);
  
  // Format for display (for backward compatibility)
  const totalNet = useMemo(() => {
    return unitsToFormattedChips(totalNetUnits);
  }, [totalNetUnits]);

  const totalPendingNet = useMemo(() => {
    let total = tallies.reduce((acc, current) => {
      const pending = current?.net != current?.net_pc ? current?.net_pc : 0;
      return acc + Number(pending ?? 0);
    }, 0);

    return unitsToFormattedChips(total);
  }, [tallies]);

  const totalNetDollar = useMemo(() => {
    if (conversionRate) {
      // Convert the string formatted value back to number for calculation
      const chipValue = parseFloat(totalNet); 
      const total = chipValue * conversionRate;
      return round(total, 2);
    }

    return 0;
  }, [totalNet, conversionRate]);

  const onItemPress = ({tally}) => {
    setTally(tally);
    setIsVisible(true);
  };

  const renderItem = ({item, index}) => (
    <TouchableWithoutFeedback
      onPress={() => {
        onItemPress({
          tally: item,
        });
      }}>
      <View
        style={[
          styles.item,
          index === tallies?.length - 1 ? styles.itemLast : null,
        ]}>
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
    <View>
      <FlatList
        ListHeaderComponent={
          <TallyHeader
            totalNet={totalNet}
            totalNetUnits={totalNetUnits}
            totalPendingNet={totalPendingNet}
            totalNetDollar={totalNetDollar}
            currencyCode={preferredCurrency.code}
            navigation={props.navigation}
            searchInput={text => onSearch(text)}
          />
        }
        ListEmptyComponent={
          <View style={styles.center}>
            <Text>No list found.</Text>
          </View>
        }
        data={filteredTallies}
        renderItem={renderItem}
        onRefresh={fetchTallies}
        keyExtractor={(_, index) => index}
        showsVerticalScrollIndicator={false}
        contentContainerStyle={styles.contentContainer}
        ListFooterComponent={<View style={styles.footer} />}
        refreshing={
          // adding this condition as wm will not return anything unless connected
          status !== connectionStatus.connected ? false : fetching
        }
      />

      <PayModal
        tally={tally}
        visible={isVisible}
        navigation={props.navigation}
        onClose={() => setIsVisible(false)}
        conversionRate={conversionRate}
      />
    </View>
  );
};

const styles = StyleSheet.create({
  contentContainer: {
    paddingBottom: 16,
    backgroundColor: colors.white,
  },
  item: {
    width: '90%',
    paddingVertical: 18,
    alignSelf: 'center',
    borderBottomWidth: 1,
    paddingHorizontal: 12,
    borderBottomColor: colors.lightgray,
  },
  itemLast: {
    borderBottomWidth: 0,
  },
  footer: {
    paddingBottom: 30,
    backgroundColor: colors.white,
  },
  center: {
    alignItems: 'center',
    justifyContent: 'center',
  },
});

export default Tally;
