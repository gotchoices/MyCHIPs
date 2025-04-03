import React, { useMemo } from 'react';
import { View, Text, StyleSheet } from 'react-native';
import PropTypes from 'prop-types';
import { useSelector } from 'react-redux';

import { colors } from '../../config/constants';
import { round, unitsToFormattedChips } from '../../utils/common';
import { ChitIcon } from '../SvgAssets/SvgAssets';
import { getIntegerValue, getDecimalValue } from '../../utils/user';

/**
 * A standardized component for displaying CHIP values with consistent styling
 * 
 * Features:
 * - Splits integer and decimal parts with different styling
 * - Can automatically calculate and show currency conversion value
 * - Supports different sizes (small, medium, large)
 * - Applies color coding based on value sign
 * - Displays ChitIcon with appropriate color
 * - Takes milliCHIP units as input and handles formatting internally
 */
const ChipValue = ({
  units,
  currencyValue: externalCurrencyValue,
  currencyCode: externalCurrencyCode,
  showCurrency = true,
  calculateCurrency = true, // Default to internal conversion
  size = 'medium',
  showIcon = true,
  iconSize,
  style
}) => {
  // Convert units to formatted chip value
  const displayValue = unitsToFormattedChips(units || 0);
  
  // Determine if the value is negative for styling
  const isNegative = parseFloat(displayValue) < 0;
  
  // Get the integer and decimal portions
  const integerPart = getIntegerValue(displayValue);
  const decimalPart = getDecimalValue(displayValue);

  // Generate size-based styles
  const sizeStyles = getSizeStyles(size);
  
  // Determine icon dimensions based on size or explicit props
  const iconDimensions = iconSize || {
    width: sizeStyles.iconSize,
    height: sizeStyles.iconSize
  };
  
  // Get currency data from Redux if needed
  const { preferredCurrency } = useSelector(state => state.profile || {});
  const { conversionRate } = useSelector(state => state.chipCurrency || { conversionRate: 0 });
  
  // Calculate currency display values
  const currencyInfo = useMemo(() => {
    // If not showing currency, return undefined
    if (!showCurrency) {
      return { currencyValue: undefined, currencyCode: undefined };
    }
    
    // If using external values, use those
    if (!calculateCurrency || !conversionRate) {
      return { 
        currencyValue: externalCurrencyValue, 
        currencyCode: externalCurrencyCode 
      };
    }
    
    // Otherwise calculate internally
    const chipNumber = parseFloat(displayValue);
    const currencyValue = round(chipNumber * conversionRate, 2);
    
    return {
      currencyValue,
      currencyCode: preferredCurrency?.code
    };
  }, [
    showCurrency, 
    calculateCurrency, 
    externalCurrencyValue, 
    externalCurrencyCode, 
    conversionRate, 
    displayValue, 
    preferredCurrency
  ]);

  return (
    <View style={[styles.container, style]}>
      {/* Currency value */}
      {currencyInfo.currencyValue !== undefined && currencyInfo.currencyCode && (
        <Text style={styles.currencyText}>
          {currencyInfo.currencyCode} {currencyInfo.currencyValue}
        </Text>
      )}
      
      {/* CHIP value display */}
      <View style={styles.chipContainer}>
        {/* Optional ChitIcon */}
        {showIcon && (
          <ChitIcon
            color={isNegative ? colors.red : colors.green}
            width={iconDimensions.width}
            height={iconDimensions.height}
          />
        )}
        
        {/* Integer part */}
        <Text 
          style={[
            styles.integerPart,
            sizeStyles.integerText,
            isNegative ? styles.negativeText : styles.positiveText
          ]}
        >
          {integerPart}
        </Text>
        
        {/* Decimal part */}
        <Text 
          style={[
            styles.decimalPart,
            sizeStyles.decimalText,
            isNegative ? styles.negativeText : styles.positiveText
          ]}
        >
          {decimalPart}
        </Text>
      </View>
    </View>
  );
};

// Size presets for different contexts
const getSizeStyles = (size) => {
  switch (size) {
    case 'small':
      return {
        integerText: {
          fontSize: 16,
          lineHeight: 16,
        },
        decimalText: {
          fontSize: 10,
          lineHeight: 10,
          paddingBottom: 6,
        },
        iconSize: 12
      };
    case 'large':
      return {
        integerText: {
          fontSize: 32,
          lineHeight: 32,
        },
        decimalText: {
          fontSize: 16,
          lineHeight: 16,
          paddingBottom: 10,
        },
        iconSize: 18
      };
    case 'medium':
    default:
      return {
        integerText: {
          fontSize: 22,
          lineHeight: 22,
        },
        decimalText: {
          fontSize: 12,
          lineHeight: 12,
          paddingBottom: 8,
        },
        iconSize: 14
      };
  }
};

const styles = StyleSheet.create({
  container: {
    alignItems: 'flex-end',
  },
  chipContainer: {
    flexDirection: 'row',
    alignItems: 'center',
  },
  currencyText: {
    fontFamily: 'inter',
    fontSize: 12,
    color: colors.gray300,
    marginBottom: 2,
  },
  integerPart: {
    fontFamily: 'inter',
    fontWeight: '600',
    marginHorizontal: 2,
  },
  decimalPart: {
    fontFamily: 'inter',
    textDecorationLine: 'underline',
  },
  positiveText: {
    color: colors.green,
  },
  negativeText: {
    color: colors.red,
  },
});

ChipValue.propTypes = {
  units: PropTypes.oneOfType([PropTypes.string, PropTypes.number]),
  currencyValue: PropTypes.oneOfType([PropTypes.string, PropTypes.number]),
  currencyCode: PropTypes.string,
  showCurrency: PropTypes.bool,
  calculateCurrency: PropTypes.bool,
  size: PropTypes.oneOf(['small', 'medium', 'large']),
  showIcon: PropTypes.bool,
  iconSize: PropTypes.shape({
    width: PropTypes.number,
    height: PropTypes.number
  }),
  style: PropTypes.object
};

export default ChipValue;