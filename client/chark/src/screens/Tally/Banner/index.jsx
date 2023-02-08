import React, { useEffect } from 'react';
import { View, StyleSheet, Text, Image, TouchableWithoutFeedback } from 'react-native';

import { colors } from '../../../config/constants';
import visualBtn from '../../../../assets/visual-button.png';
import avatarImg from '../../../../assets/report-profile.png';
import mychips from '../../../../assets/mychips-large.png';
import useCurrentUser from '../../../hooks/useCurrentUser';

const Banner = (props) => {
  const { user } = useCurrentUser();

  const navigateToReport = () => {
    props.navigation.navigate('TallyReport')
  }

  return (
    <View style={styles.container}>
      <View style={styles.header}>
        <Text style={styles.headerText}>Tally Report</Text>
        <TouchableWithoutFeedback
          onPress={navigateToReport}
        >
          <Image source={visualBtn} />
        </TouchableWithoutFeedback>
      </View>

      <View style={{ alignItems: 'center' }}>
        <View style={styles.balanceContainer}>
          <View style={styles.balance}>
            <Image source={avatarImg} style={{ opacity: 1 }} />

            <View style={{ alignItems: 'center' }}>
              <Text>Net CHIP balance</Text>

              <View style={{ flexDirection: 'row', alignItems: 'center' }}>
                <Image source={mychips} />
                <Text style={props.totalNet < 0 ? styles.mychipsNetNeg : styles.mychipsNet}>
                  {props.totalNet}
                </Text>
              </View>
              <Text>${props.totalNetDollar} USD</Text>
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
    padding: 32,
  },
  header: {
    flexDirection: 'row',
    justifyContent: 'space-between',
    alignItems: 'center',
  },
  headerText: {
    fontSize: 24,
    fontWeight: '700',
    color: colors.white,
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
