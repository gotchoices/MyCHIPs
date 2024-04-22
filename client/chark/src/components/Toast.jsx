import React from 'react';
import Toast, { BaseToast } from "react-native-toast-message";

import { colors } from '../config/constants';

export const toastConfig = {
  success: (props) => (
    <BaseToast
      {...props}
      text1NumberOfLines={3}
      style={[
        {
          borderLeftColor: colors.green,
        },
      ]}
    />
  ),
  error: (props) => (
    <BaseToast
      {...props}
      text1NumberOfLines={3}
      style={[
        {
          borderLeftColor: colors.red,
        },
      ]}
    />
  ),
  warning: (props) => (
    <BaseToast
      {...props}
      text1NumberOfLines={3}
      style={[
        {
          borderLeftColor: colors.yellow,
        },
      ]}
    />
  ),
};

const CustomToast = () => {
  return (
    <Toast config={toastConfig} />
  )
}

export default CustomToast;

