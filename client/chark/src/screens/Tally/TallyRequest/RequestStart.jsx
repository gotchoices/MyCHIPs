import React from 'react';
import PropTypes from 'prop-types';
import { 
  View,
  Text,
  StyleSheet,
} from 'react-native';

import Header from './Header';
import Button from '../../../components/Button';
import CloseIcon from '../../../../assets/svg/ic_close.svg';

import { colors } from '../../../config/constants';

const RequestStart = (props) => {
  const agent = props.agent ?? '';
  const agentLength = agent.length;
  const _agent = agentLength >= 24 
    ? agent.slice(0, 15) + '...' + agent.slice(agentLength - 4, agentLength)
    : agent;

  const commonText = props?.commonText;

  const onClose = () => {
    props.navigation?.navigate('Home');
  }

  return (
    <View style={styles.container}>
      <Header headerText="Tally Request">
        <CloseIcon 
          onPress={onClose}
        />
      </Header>
      
      <View style={styles.content}>
        <Text style={styles.agent}>
          {_agent}
        </Text>

        <Text style={styles.name}>
          {props.name}
        </Text>

        <Text style={styles.description}>
          {commonText?.invited?.help}
        </Text>

      </View>

      <Button
        title="Start"
        onPress={props.onStart}
      />

    </View>
  )
}

const font = {
  fontFamily: 'inter',
  fontWeight: '500',
}

const styles = StyleSheet.create({
  container: {
    flex: 1,
  },
  content: {
    flex: 1,
    width: '100%',
    justifyContent: 'center',
    alignItems: 'center',
  },
  agent: {
    ...font,
    fontSize: 14,
    color: colors.gray300,
    marginTop: 10,
    marginBottom: 5,
  },
  name: {
    ...font,
    fontSize: 35,
    color: colors.black,
    marginVertical: 5,
  },
  description: {
    ...font,
    fontSize: 20,
    color: colors.gray300,
    marginTop: 5,
    textAlign: 'center',
  }
});

RequestStart.propTypes = {
  style: PropTypes.object,
  agent: PropTypes.string.isRequired,
  name: PropTypes.string.isRequired,
  onStart: PropTypes.func.isRequired,
  navigation: PropTypes.any,
  commonText: PropTypes.object,
}

export default RequestStart;
