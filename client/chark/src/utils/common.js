import 'react-native-get-random-values';
import { v4 as uuidv4, v5 as uuidv5 } from 'uuid';
import moment from 'moment';
import { CHIP_UNIT_FACTOR, CHIP_DECIMAL_PLACES } from '../config/constants';

export const round = (value, decimals) => {
  const temp = parseFloat(value + `e+${decimals}`);
  const result = Math.round(temp) + `e-${decimals}`;
  return parseFloat(result).toFixed(decimals);
}

/**
 * Converts a floating-point CHIP value to integer milliCHIPs units
 * @param {number|string} chipValue - CHIP value with decimal places
 * @returns {number} Integer representing milliCHIPs units
 */
export const chipsToUnits = (chipValue) => {
  if (chipValue === null || chipValue === undefined || chipValue === '') {
    return 0;
  }
  
  // Parse the input to ensure it's a number
  const value = parseFloat(chipValue);
  if (isNaN(value)) {
    return 0;
  }
  
  // Convert to integer units
  return Math.round(value * CHIP_UNIT_FACTOR);
}

/**
 * Formats a CHIP value with the correct number of decimal places
 * @param {number|string} chipValue - CHIP value to format
 * @returns {string} Formatted CHIP value with proper decimal places
 */
export const formatChipValue = (chipValue) => {
  if (chipValue === null || chipValue === undefined || chipValue === '') {
    return '0.000';
  }
  
  const value = parseFloat(chipValue);
  if (isNaN(value)) {
    return '0.000';
  }
  
  return value.toFixed(CHIP_DECIMAL_PLACES);
}

/**
 * Converts integer units (milliCHIPs) to floating-point CHIP value
 * @param {number|string} units - Integer units value
 * @returns {number} Floating-point CHIP value
 */
export const unitsToChips = (units) => {
  if (units === null || units === undefined || units === '') {
    return 0;
  }
  
  const value = parseInt(units);
  if (isNaN(value)) {
    return 0;
  }
  
  // Convert from units to CHIPs
  return value / CHIP_UNIT_FACTOR;
}

/**
 * Converts integer units to a formatted CHIP string with fixed decimal places
 * @param {number|string} units - Integer units value
 * @returns {string} Formatted CHIP value with exactly 3 decimal places
 */
export const unitsToFormattedChips = (units) => {
  const chipValue = unitsToChips(units);
  return formatChipValue(chipValue);
}

export const random = () => {
  const randomStr = (new Date()).getTime().toString(36)
  const uuid = uuidv4();
  return `${uuid}_${randomStr}`
}

export const getLinkHost = (url) => {
  return url?.split('?')?.[0]?.split('://')?.[1] ?? '';
}

export const isNil = (value) => {
  if(value === undefined || value === null)  {
    return true;
  }

  return false;
}

/**
 * Generates a standard format ISO timestamp for database operations in UTC
 * @returns {string} ISO formatted date string YYYY-MM-DDTHH:mm:ss.SSSZ in UTC
 */
export const generateTimestamp = () => {
  return moment().utc().format('YYYY-MM-DDTHH:mm:ss.SSS') + 'Z';
}

/**
 * Generates a consistent UUID v5 based on input parameters and current time
 * Can be used for tallies, chits, or any other entity that needs a UUID
 * @param {string} baseId - Base identifier (e.g., tally_uuid, connection ID)
 * @param {string} [namespace=uuidv5.URL] - UUID namespace to use
 * @param {string} [additionalContext=''] - Optional context for more uniqueness
 * @returns {string} UUID v5 based on input parameters
 */
export const generateUuid = (baseId, namespace = uuidv5.URL, additionalContext = '') => {
  // First create a base UUID from the provided baseId and namespace
  const baseUuid = uuidv5(baseId, namespace);
  
  // Create the seed string using current time, a random number, and additional context
  const seedString = generateTimestamp() + Math.random().toString() + additionalContext;
  
  // Generate final UUID using the seed string and base UUID as namespace
  return uuidv5(seedString, baseUuid);
}
