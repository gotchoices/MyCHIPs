import React from 'react';
import PropTypes from 'prop-types';
import { ActivityIndicator, Text, View } from 'react-native';

import { colors } from '../../config/constants';

const Spinner = (props) => {
  return (
    <>
      <ActivityIndicator 
        size={props.size ?? 'large'}
        color={props.color ?? colors.blue}
      />

      {
        props.text && <Text>{props.text}</Text>
      }
    </>
  )
}

Spinner.propTypes = {
  size: PropTypes.string,
  color: PropTypes.string,
  text: PropTypes.string,
}

export default Spinner;
