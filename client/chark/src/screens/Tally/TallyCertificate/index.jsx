import React, { useMemo, useEffect } from "react"
import { ScrollView, StyleSheet, Text, View } from "react-native"

import HelpText from '../../../components/HelpText';
import DefaultCertificate from './DefaultCertificate';

import { colors } from "../../../config/constants";

const TallyCertificate = (props) => {
  const { data } = props.route?.params ?? {};

  useEffect(() => {
    props.navigation.setOptions({
      title: data?.title ?? "Tally Certificate",
    });
  }, []);

  const name = Object.values((data?.name ?? {})).join(' ')
  const cid = data?.chad?.cid ?? '';
  const agent = data?.chad?.agent ?? '';
  const email = useMemo(() => {
    const found = (data?.connect ?? []).find(connect => connect.media === 'email')
    return found?.address ?? ''
  }, [data?.connect])

  return (
    <ScrollView
      style={styles.container}
      contentContainerStyle={styles.contentContainer}
    >
      <DefaultCertificate
        name={name}
        cid={cid}
        email={email}
        agent={agent}
      />
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
