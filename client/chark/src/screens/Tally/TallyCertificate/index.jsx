import React, { useMemo, useEffect } from "react"
import { ScrollView, StyleSheet, Text, View } from "react-native"

import HelpText from '../../../components/HelpText';
import { colors } from "../../../config/constants";

const TallyCertificate = (props) => {
  const { data } = props.route?.params ?? {};

  useEffect(() => {
    props.navigation.setOptions({
      title: data?.title ?? "Tally Certificate",
    });
  }, []);

  const name = Object.values((data?.name ?? {})).join(' ')
  const cid = data?.chad?.cid;
  const agent = data?.chad?.agent;
  const email = useMemo(() => {
    const found = (data?.connect ?? []).find(connect => connect.media === 'email')
    return found?.address ?? ''
  }, [data?.connect])

  return (
    <ScrollView
      style={styles.container}
      contentContainerStyle={styles.contentContainer}
    >
      <View style={styles.detailControl}>
        <HelpText
          label={'Formal Name'}
        />
        
        <Text style={styles.text}>
          {name}
        </Text>
      </View>

      <View style={styles.detailControl}>
        <HelpText
          label={'CID'}
        />
        
        <Text style={styles.text}>
          {cid}
        </Text>
      </View>

      <View style={styles.detailControl}>
        <HelpText
          label={'Email'}
        />
        
        <Text style={styles.text}>
          {email}
        </Text>
      </View>

      <View style={styles.detailControl}>
        <HelpText
          label={'Agent'}
        />
        
        <Text style={styles.text}>
          {agent}
        </Text>
      </View>
    </ScrollView>
  )
}

const styles = StyleSheet.create({
  container: {
    flex: 1,
    margin: 20,
  },
  detailControl: {
    marginBottom: 10,
  },
  text: {
    color: colors.black,
    fontSize: 14,
    fontFamily: 'inter',
  },
});

export default TallyCertificate;
