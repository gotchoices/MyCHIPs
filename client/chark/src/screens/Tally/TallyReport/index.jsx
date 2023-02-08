import React from 'react';
import { View, StyleSheet, TouchableWithoutFeedback, Text, Image } from 'react-native';

import tabularBtn from '../../../../assets/tabular-button.png';

import constants, { colors } from '../../../config/constants';
import CustomText from '../../../components/CustomText';

const TallyReport = (props) => {

  const navigateBalanceSheet = () => {
    props.navigation.navigate('Home');
  }

  return (
    <View style={styles.container}>
      <View style={styles.header}>
        <CustomText as="h2" style={styles.headerText}>
          Tally Report
        </CustomText>

        <TouchableWithoutFeedback
          onPress={navigateBalanceSheet}
        >
          <Image
            source={tabularBtn}
          />
        </TouchableWithoutFeedback>

      </View>

      <View style={styles.reportView}>
        <Text>Tally report diagram</Text>
      </View>
    </View>
  )
}

const styles = StyleSheet.create({
  container: {
    flex: 1,
    backgroundColor: colors.gray700,
    marginBottom: 55,
  },
  header: {
    margin: 20,
    flexDirection: 'row',
    justifyContent: 'space-between',
    alignItems: 'center',
  },
  headerText: {
    color: colors.white,
  },
  reportView: {
    alignItems: 'center',
    justifyContent: 'center',
    marginTop: '12%',
    backgroundColor: colors.white,
    width: '60%',
    height: '60%',
    alignSelf: 'center',
  }
});


export default TallyReport;
