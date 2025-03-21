/**
 * User-related utility functions for data fetching and tally management.
 * 
 * This file provides utilities for:
 * 1. Fetching the current user from the backend
 * 2. Formatting and displaying tally partner names
 * 3. Sorting tallies by different criteria
 * 4. Formatting numeric values for display
 */

// Counter to ensure each request gets a unique identifier
let pktId = 1;

/**
 * Queries the backend for current user information.
 * 
 * This function fetches the currently authenticated user entity from the
 * base.curr_eid table, which contains the user's ID and other essential info.
 * It's typically called when the app first connects to establish the user context.
 * 
 * @param {Object} wm - Wyseman client instance for backend communication
 * @returns {Promise<Array>} - Resolves to an array containing the user entity object
 */
export function query_user(wm) {
  return new Promise((resolve, reject) => {
    wm.request(
      pktId++,
      'select',
      {
        view: 'base.ent_v',
        table: 'base.curr_eid',
        params: [],
      },
      (data, err) => {
        if (err) {
          return reject(err);
        }
        resolve(data);
      },
    );
  });
}

/**
 * Formats a tally partner's name for display.
 * 
 * Handles both organizational entities (type 'o') and personal entities,
 * creating a properly formatted name string from the available fields.
 * Organizations use their full name, while people get a formatted first/middle/surname.
 * 
 * @param {Object} item - Tally item containing partner certificate data
 * @returns {string} - Formatted name for display
 */
export const getTallyName = item => {
  if (item.part_cert?.type === 'o') {
    return `${item.part_cert?.name}`;
  }

  const {first, middle, surname} = item.part_cert?.name || {};
  return `${first || ''}${middle ? ' ' + middle + ' ' : ''}${surname || ''}`;
};

/**
 * Sorts a list of tallies alphabetically by partner name.
 * 
 * Creates a new sorted array without modifying the original.
 * Uses the localeCompare method for proper international string comparison.
 * 
 * @param {Array} tallies - Array of tally objects
 * @returns {Array} - New array sorted alphabetically by partner name
 */
export const sortTalliesAlphabetically = tallies => {
  const sortedArray = [...tallies].sort((a, b) => {
    const tallyName1 = getTallyName(a);
    const tallyName2 = getTallyName(b);

    return tallyName1.localeCompare(tallyName2);
  });

  return sortedArray;
};

/**
 * Sorts a list of tallies by a specified field with directional control.
 * 
 * Intelligently handles different data types:
 * - Dates are parsed into Date objects for chronological sorting
 * - Numeric fields are converted to numbers for numeric sorting
 * 
 * @param {Array} tallies - Array of tally objects
 * @param {string} field - Field name to sort by (e.g., 'tally_date', 'net')
 * @param {boolean} descending - If true, sort in descending order
 * @returns {Array} - New array sorted by the specified field
 */
export const sortTallies = (tallies, field, descending = false) => {
  const sorteTallies = tallies.slice().sort((a, b) => {
    const valueA =
      field === 'tally_date' ? new Date(a[field]) : parseFloat(a[field]);

    const valueB =
      field === 'tally_date' ? new Date(b[field]) : parseFloat(b[field]);

    return descending ? valueB - valueA : valueA - valueB;
  });

  return sorteTallies;
};

/**
 * Extracts the integer portion from a decimal value.
 * 
 * Used for display formatting when showing currency values
 * where the integer and decimal parts need separate styling.
 * Handles various input types safely.
 * 
 * @param {string|number} amount - Decimal value (e.g., "123.45" or 123.45)
 * @returns {string} - The integer portion ("123"), or "0" if invalid input
 */
export const getIntegerValue = amount => {
  if (!amount && amount !== 0) return '0';
  const parts = String(amount).split('.');
  return parts[0] || '0';
};

/**
 * Extracts the decimal portion from a decimal value.
 * 
 * Used for display formatting when showing currency values
 * where the integer and decimal parts need separate styling.
 * Handles various input types safely.
 * 
 * @param {string|number} amount - Decimal value (e.g., "123.45" or 123.45)
 * @returns {string} - The decimal portion ("45"), or "0" if no decimal part
 */
export const getDecimalValue = amount => {
  if (!amount && amount !== 0) return '0';
  const parts = String(amount).split('.');
  return parts[1] || '0';
};
