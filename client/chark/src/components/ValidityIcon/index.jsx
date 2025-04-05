import React, { useState } from 'react';
import PropTypes from 'prop-types';
import { View, Text, TouchableWithoutFeedback } from 'react-native';
import Tooltip from 'react-native-walkthrough-tooltip';
import { colors } from '../../config/constants';
import GreenTick from '../../../assets/svg/green_tick.svg';
import WarningIcon from '../../../assets/svg/warning_icon.svg';
import useMessageText from '../../hooks/useMessageText';

/**
 * ValidityIcon component that shows a green check for valid items and warning for invalid
 * with optional tooltips explaining the status
 * 
 * @param {Object} props
 * @param {string} props.status - 'valid', 'warning', 'invalid', or undefined if not applicable
 * @param {number} props.size - size of the icon
 * @param {boolean} props.showTooltip - whether to show tooltip on press
 * @param {string} props.msgView - the message view to use for tooltip text (e.g., 'tallies_v_me')
 * @param {string} props.msgTag - the message tag to use for tooltip text (e.g., 'nocert', 'nosig')
 */
const ValidityIcon = ({ 
  status, 
  size = 16, 
  showTooltip = false,
  msgView = 'tallies_v_me',
  msgTag = null
}) => {
  const [isVisible, setIsVisible] = useState(false);
  const { messageText } = useMessageText();
  
  // If status is undefined or null, don't show any icon
  if (!status) {
    return null;
  }

  // Only show tooltip for non-valid statuses
  const shouldShowTooltip = showTooltip && status !== 'valid' && msgTag;
  
  // Get tooltip message from the specified view and tag
  const getTooltipContent = () => {
    if (!shouldShowTooltip) return null;
    
    const msgViewObj = messageText?.[msgView]?.msg;
    // If message exists in DB, use it; otherwise default to "Invalid"
    return msgViewObj?.[msgTag]?.help || "Invalid";
  };
  
  const tooltipContent = getTooltipContent();
  
  // Render just the icon if no tooltip
  if (!shouldShowTooltip || !tooltipContent) {
    if (status === 'valid') {
      return <GreenTick width={size} height={size} />;
    } else {
      return <WarningIcon width={size} height={size} />;
    }
  }
  
  // Render icon with tooltip
  return (
    <Tooltip
      isVisible={isVisible}
      content={<Text style={styles.tooltipText}>{tooltipContent}</Text>}
      contentStyle={styles.tooltipContent}
      placement="top"
      onClose={() => setIsVisible(false)}
    >
      <TouchableWithoutFeedback 
        onPress={() => setIsVisible(true)}
      >
        <View style={{ padding: 4 }}>
          {status === 'valid' 
            ? <GreenTick width={size} height={size} />
            : <WarningIcon width={size} height={size} />
          }
        </View>
      </TouchableWithoutFeedback>
    </Tooltip>
  );
};

const styles = {
  tooltipContent: {
    backgroundColor: colors.white,
    borderRadius: 8,
    padding: 8,
  },
  tooltipText: {
    color: colors.black,
    fontSize: 12,
    fontFamily: 'inter',
  },
};

ValidityIcon.propTypes = {
  status: PropTypes.string,
  size: PropTypes.number,
  showTooltip: PropTypes.bool,
  msgView: PropTypes.string,
  msgTag: PropTypes.string
};

export default ValidityIcon;