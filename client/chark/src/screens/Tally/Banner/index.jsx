import React, {useMemo} from 'react';
import {
  View,
  Text,
  StyleSheet,
  Dimensions,
  TouchableOpacity,
} from 'react-native';
import {useSelector} from 'react-redux';

import {colors} from '../../../config/constants';
import {isNil} from '../../../utils/common';
import useMessageText from '../../../hooks/useMessageText';

import Header from '../Header';
import Avatar from '../../../components/Avatar';
import ChipValue from '../../../components/ChipValue';
import {
  FilterSecondIcon,
  VisualIcon,
} from '../../../components/SvgAssets/SvgAssets';
import Activity from '../Activity';

const Banner = props => {
  const {avatar, personal} = useSelector(state => state.profile);
  const {messageText} = useMessageText();
  const talliesMeMessageText = messageText?.tallies_v_me?.msg;
  const chitMeText = messageText?.chits_v_me?.col;
  const charkText = messageText?.chark?.msg;

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

  const onFilter = () => {
    props.navigation.navigate('FilterTallyScreen');
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

      {/* Future sorters row - placeholder for now */}
      <View style={styles.filtersRow}>
        <TouchableOpacity style={styles.filterContainer} onPress={onFilter}>
          <FilterSecondIcon />
          <Text style={styles.filterText}>
            {talliesMeMessageText?.sort?.title ?? ''}
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
    justifyContent: 'flex-start',
    alignItems: 'center',
    marginBottom: 10,
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
  filterText: {
    fontSize: 12,
    marginStart: 4,
    color: '#636363',
    fontFamily: 'inter',
  },
});

export default Banner;
