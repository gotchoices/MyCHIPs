import React, {useMemo} from 'react';
import {View, Text, StyleSheet} from 'react-native';
import PropTypes from 'prop-types';
import {useSelector} from 'react-redux';

import {colors} from '../../../config/constants';
import {unitsToFormattedChips, unitsToChips, round} from '../../../utils/common';

import Avatar from '../../../components/Avatar';
import ChipValue from '../../../components/ChipValue';
import {Warning_16} from '../../../components/SvgAssets/SvgAssets';
import {needsWarningIndicator} from '../../../utils/tally-verification';
import {formatRandomString} from '../../../utils/format-string';
import useMessageText from '../../../hooks/useMessageText';

const TallyItem = props => {
  const tally = props.tally;
  // Get validation status from Redux store if available
  const validityStatuses = useSelector(state => state.updateTally.validityStatuses || {});
  const reduxValidityStatus = tally?.tally_uuid ? validityStatuses[tally.tally_uuid] : undefined;
  
  // Use the Redux status if available, otherwise fall back to the tally's direct status
  const validityStatus = reduxValidityStatus || tally.validityStatus;
  
  // Get the tally's partner certificate
  const partCert = tally?.part_cert;
  const partName =
    partCert?.type === 'o'
      ? `${partCert?.name}`
      : `${partCert?.name?.first}${
          partCert?.name?.middle ? ' ' + partCert?.name?.middle + ' ' : ''
        } ${partCert?.name?.surname}`;

  // Convert values to numbers for comparison to handle type differences
  const netValue = Number(tally?.net ?? 0);
  const netPcValue = Number(tally?.net_pc ?? 0);
  const hasPendingChit = !!tally?.net_pc && netValue !== netPcValue;

  const {messageText} = useMessageText();
  const chitMeText = messageText?.chits_v_me?.col;
  const pendingText = useMemo(() => {
    return chitMeText?.status?.values?.find(s => s.value === 'pend');
  }, [chitMeText?.status?.values]);

  return (
    <View style={styles.container}>
      <Avatar style={styles.avatar} avatar={props.image} />

      <View style={{flex: 1}}>
        <View style={{flexDirection: 'row', justifyContent: 'space-between', alignItems: 'center'}}>
          <Text style={styles.name}>{partName}</Text>
          {needsWarningIndicator(validityStatus) && (
            <Warning_16 size={18} />
          )}
        </View>
        <Text style={[styles.description, {marginTop: 4}]}>
          {partCert?.chad?.cuid}:{formatRandomString(partCert?.chad?.agent)}
        </Text>
      </View>

      <View style={styles.price}>
        {hasPendingChit && (
          <View style={styles.pendingView}>
            <Text style={styles.pending}>
              {pendingText?.title ?? ''} Chips
            </Text>
          </View>
        )}
        
        {/* Using the new ChipValue component with internal currency conversion */}
        <ChipValue 
          units={tally?.net ?? 0}
          size="medium"
          showIcon={true}
          showCurrency={true}
          iconSize={{width: 18, height: 18}}
        />
      </View>
    </View>
  );
};

const font = {
  fontFamily: 'inter',
};

const styles = StyleSheet.create({
  container: {
    flexDirection: 'row',
    justifyContent: 'space-between',
  },
  profile: {
    flexDirection: 'row',
  },
  avatar: {
    marginRight: 8,
    alignSelf: 'center',
    height: 45,
    width: 45,
    borderRadius: 45 / 2,
  },
  name: {
    ...font,
    fontSize: 16,
    fontWeight: 'bold',
  },
  description: {
    ...font,
    fontSize: 12,
    color: colors.gray500,
  },
  price: {
    ...font,
    alignItems: 'flex-end',
  },
  pending: {
    fontSize: 8,
    color: colors.gray700,
  },
  pendingView: {
    backgroundColor: colors.white200,
    padding: 5,
    borderRadius: 10,
    marginBottom: 2
  }
});

TallyItem.propTypes = {
  tally: PropTypes.object.isRequired,
  conversionRate: PropTypes.number, // Still included for backward compatibility
  currency: PropTypes.string, // Still included for backward compatibility
};

export default TallyItem;
