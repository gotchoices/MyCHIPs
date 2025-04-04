import React, {useMemo} from 'react';
import {
  View,
  Text,
  StyleSheet,
  TouchableOpacity,
} from 'react-native';
import {useSelector, useDispatch} from 'react-redux';
import Icon from 'react-native-vector-icons/FontAwesome';

import {colors} from '../../../config/constants';
import {isNil} from '../../../utils/common';
import useMessageText from '../../../hooks/useMessageText';
import {
  toggleNameSort, 
  toggleDateSort, 
  toggleBalanceSort,
  selectActiveSorter,
  selectNameSort,
  selectDateSort,
  selectBalanceSort
} from '../../../redux/tallySortSlice';

import Header from '../Header';
import Avatar from '../../../components/Avatar';
import ChipValue from '../../../components/ChipValue';
import {
  VisualIcon,
} from '../../../components/SvgAssets/SvgAssets';
import Activity from '../Activity';

const Banner = props => {
  const dispatch = useDispatch();
  const {avatar, personal} = useSelector(state => state.profile);
  const {messageText} = useMessageText();
  const talliesMeMessageText = messageText?.tallies_v_me?.msg;
  const chitMeText = messageText?.chits_v_me?.col;
  const charkText = messageText?.chark?.msg;
  
  // Get sorting state from Redux
  const activeSorter = useSelector(selectActiveSorter);
  const nameSort = useSelector(selectNameSort);
  const dateSort = useSelector(selectDateSort);
  const balanceSort = useSelector(selectBalanceSort);

  const navigateToReport = () => {
    props.navigation?.navigate?.('TallyReport');
  };

  const navigateToNotification = () => {
    props.navigation?.navigate?.('Activity');
  };

  const pendingText = useMemo(() => {
    return chitMeText?.status?.values?.find(s => s.value === 'pend');
  }, [chitMeText?.status?.values]);

  const hasPendingTotal =
    !isNil(props.totalPendingNet) &&
    props.totalPendingNet != 0.0 &&
    props.totalPendingNet != props.totalNet; // If pending net and total net are equal, then the tally does not have pending chits
    
  // Handle sort actions
  const onNameSort = () => {
    dispatch(toggleNameSort());
  };
  
  const onDateSort = () => {
    dispatch(toggleDateSort());
  };
  
  const onBalanceSort = () => {
    dispatch(toggleBalanceSort());
  };

  return (
    <View style={styles.container}>
      <Header
        leftIcon={<VisualIcon />}
        title={charkText?.mychips?.title ?? ''}
        onClick={navigateToReport}
        onNavigateToNotification={navigateToNotification}
        rightIcon={<Activity />}
      />

      <View style={styles.headerRow}>
        {/* Left section: Avatar and name (centered) */}
        <View style={styles.avatarSection}>
          <Avatar avatar={avatar} />
          <Text style={styles.name}>{personal?.cas_name ?? ''}</Text>
        </View>
        
        {/* Right section: Grand total (right-aligned) */}
        <View style={styles.totalSection}>
          <ChipValue 
            units={props.totalNetUnits}
            size="large"
            showIcon={true}
            showCurrency={true}
            iconSize={{width: 24, height: 24}}
          />
        </View>
      </View>

      {/* Sorters row with three sort options */}
      <View style={styles.filtersRow}>
        {/* Name Sorter (left) */}
        <TouchableOpacity 
          style={[
            styles.filterContainer, 
            activeSorter === 'name' && styles.activeFilter
          ]} 
          onPress={onNameSort}
        >
          <Icon 
            name={nameSort.direction === 'asc' ? "sort-alpha-asc" : "sort-alpha-desc"} 
            size={14} 
            color={activeSorter === 'name' ? colors.primary : "#636363"} 
          />
          <Text style={[
            styles.filterText,
            activeSorter === 'name' && styles.activeFilterText
          ]}>
            {talliesMeMessageText?.part_cert?.title || "Name"}
          </Text>
        </TouchableOpacity>
        
        {/* Date Sorter (middle) */}
        <TouchableOpacity 
          style={[
            styles.filterContainer, 
            activeSorter === 'date' && styles.activeFilter
          ]} 
          onPress={onDateSort}
        >
          <Icon 
            name={dateSort.direction === 'asc' ? "sort-amount-asc" : "sort-amount-desc"} 
            size={14} 
            color={activeSorter === 'date' ? colors.primary : "#636363"} 
          />
          <Text style={[
            styles.filterText,
            activeSorter === 'date' && styles.activeFilterText
          ]}>
            {talliesMeMessageText?.tally_date?.title || "Date"}
          </Text>
        </TouchableOpacity>
        
        {/* Balance Sorter (right) */}
        <TouchableOpacity 
          style={[
            styles.filterContainer, 
            activeSorter === 'balance' && styles.activeFilter
          ]} 
          onPress={onBalanceSort}
        >
          <Icon 
            name={
              balanceSort.direction === 'abs' 
                ? "calculator" 
                : balanceSort.direction === 'asc' 
                  ? "sort-numeric-asc" 
                  : "sort-numeric-desc"
            } 
            size={14} 
            color={activeSorter === 'balance' ? colors.primary : "#636363"} 
          />
          <Text style={[
            styles.filterText,
            activeSorter === 'balance' && styles.activeFilterText
          ]}>
            {talliesMeMessageText?.net?.title || "Balance"}
          </Text>
        </TouchableOpacity>
      </View>
    </View>
  );
};

const font = {
  fontFamily: 'inter',
};

const styles = StyleSheet.create({
  container: {
    marginHorizontal: 10,
  },
  // New header row with avatar and total
  headerRow: {
    flexDirection: 'row',
    justifyContent: 'space-between',
    alignItems: 'center',
    marginTop: 20,
    marginBottom: 20,
    paddingHorizontal: 10,
  },
  // Avatar and name section (left side)
  avatarSection: {
    flex: 1,
    alignItems: 'center',
    justifyContent: 'center',
  },
  // Total section (right side)
  totalSection: {
    alignItems: 'flex-end',
    justifyContent: 'center',
  },
  // Row for filter controls
  filtersRow: {
    flexDirection: 'row',
    justifyContent: 'space-between',
    alignItems: 'center',
    marginBottom: 5, // Reduced from 10 (50% reduction)
    paddingHorizontal: 10,
  },
  name: {
    ...font, 
    paddingTop: 10, 
    fontSize: 16, 
    fontWeight: '600',
    textAlign: 'center',
  },
  pending: {
    ...font,
    fontSize: 12,
  },
  filterContainer: {
    height: 30,
    borderWidth: 1,
    borderRadius: 20,
    paddingVertical: 3,
    flexDirection: 'row',
    alignItems: 'center',
    paddingHorizontal: 12,
    justifyContent: 'center',
    borderColor: colors.white100,
    backgroundColor: colors.white200,
  },
  activeFilter: {
    borderColor: colors.primary,
    backgroundColor: colors.white, // Lighter background for active filter
  },
  filterText: {
    fontSize: 12,
    marginStart: 4,
    color: '#636363',
    fontFamily: 'inter',
  },
  activeFilterText: {
    color: colors.primary,
    fontWeight: '500',
  },
});

export default Banner;
