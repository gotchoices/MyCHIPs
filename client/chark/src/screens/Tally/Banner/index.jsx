import React from 'react';
import { View, StyleSheet, Text, Image } from 'react-native';

import { colors } from '../../../config/constants';
import visualBtn from '../../../../assets/visual-button.png';
import mychips from '../../../../assets/mychips-large.png';
import mychipsNeg from '../../../../assets/mychips-red-large.png';
import useProfile from '../../../hooks/useProfile';

import Header from '../Header';
import Avatar from '../../../components/Avatar';
import { ChitIcon, VisualIcon } from '../../../components/SvgAssets/SvgAssets';

const Banner = (props) => {
  const { avatar, personal } = useProfile();

  const navigateToReport = () => {
    props.navigation?.navigate?.('TallyReport')
  }

  const isNetNegative = props.totalNet < 0;

  return (
    <View style={styles.container}>
      <Header
        icon={<VisualIcon />}
        title="Tally Report"
        onClick={navigateToReport}
      />

      <View style={{ alignItems: 'center' }}>
        <View style={styles.balanceContainer}>
          <View style={styles.balance}>
            <Avatar avatar={avatar} />

            <View style={{ alignItems: 'center', marginLeft: 5 }}>
              <Text>Net CHIP balance</Text>

              <View style={{ flexDirection: 'row', alignItems: 'center' }}>
                {/* <Image source={isNetNegative ? mychipsNeg : mychips} /> */}
                <ChitIcon color={isNetNegative ? colors.red : colors.green} />
                <Text style={isNetNegative ? styles.mychipsNetNeg : styles.mychipsNet}>
                  {props.totalNet}
                </Text>
              </View>

              {
                !!props.currencyCode && <Text>{props.totalNetDollar} {props.currencyCode}</Text>
              }
            </View>
          </View>

          <Text>{personal?.cas_name ?? ''}</Text>
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
