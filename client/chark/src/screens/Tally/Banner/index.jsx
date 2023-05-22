import React, { useEffect } from 'react';
import { View, StyleSheet, Text, Image, TouchableWithoutFeedback } from 'react-native';

import { colors } from '../../../config/constants';
import visualBtn from '../../../../assets/visual-button.png';
import avatarImg from '../../../../assets/report-profile.png';
import mychips from '../../../../assets/mychips-large.png';
import mychipsNeg from '../../../../assets/mychips-red-large.png';
import useCurrentUser from '../../../hooks/useCurrentUser';
import Header from '../Header';

const Banner = (props) => {
  const { user } = useCurrentUser();

  const navigateToReport = () => {
    props.navigation?.navigate?.('TallyReport')
  }

  const isNetNegative = props.totalNet < 0;

  return (
    <View style={styles.container}>
      <Header
        icon={visualBtn}
        title="Tally Report"
        onClick={navigateToReport}
      />

      <View style={{ alignItems: 'center' }}>
        <View style={styles.balanceContainer}>
          <View style={styles.balance}>
            <Image source={avatarImg} style={{ opacity: 1 }} />

            <View style={{ alignItems: 'center' }}>
              <Text>Net CHIP balance</Text>

              <View style={{ flexDirection: 'row', alignItems: 'center' }}>
                <Image source={isNetNegative ? mychipsNeg : mychips} />
                <Text style={isNetNegative ? styles.mychipsNetNeg : styles.mychipsNet}>
                  {props.totalNet}
                </Text>
              </View>

              {
                !!props.currencyCode && <Text>{props.totalNetDollar} {props.currencyCode}</Text>
              }
            </View>
          </View>

          <Text>{user?.curr_eid ?? ''}</Text>
        </View>
      </View>
    </View>
  )
}

const mychipsNet = {
  marginLeft: 5,
  fontSize: 32,
  fontWeight: '500',
  color: colors.green,
}

const styles = StyleSheet.create({
  container: {
    height: 265,
    backgroundColor: colors.gray700,
  },
  balanceContainer: {
    borderRadius: 25,
    maxWidth: '90%',
    overflow: 'hidden',
    padding: 16,
    backgroundColor: 'rgba(206, 204, 204, 0.75)',
  },
  balance: {
    flexDirection: 'row',
    alignItems: 'center',
  },
  mychipsNet,
  mychipsNetNeg: {
    ...mychipsNet,
    color: colors.red,
  }
});


export default Banner;
