import React from 'react';
import PropTypes from 'prop-types';
import GreenTick from '../../../assets/svg/green_tick.svg';
import WarningIcon from '../../../assets/svg/warning_icon.svg';

/**
 * Simple validity icon component that shows a green check for valid items and warning for invalid
 * @param {Object} props
 * @param {string} props.status - 'valid', 'warning', 'invalid', or undefined if not applicable
 * @param {number} props.size - size of the icon
 */
const ValidityIcon = ({ status, size = 16 }) => {
  // If status is undefined or null, don't show any icon
  if (!status) {
    return null;
  }

  if (status === 'valid') {
    return <GreenTick width={size} height={size} />;
  } else {
    // Show warning icon for both 'warning' and 'invalid' status
    return <WarningIcon width={size} height={size} />;
  }
};

ValidityIcon.propTypes = {
  status: PropTypes.string,
  size: PropTypes.number
};

export default ValidityIcon;