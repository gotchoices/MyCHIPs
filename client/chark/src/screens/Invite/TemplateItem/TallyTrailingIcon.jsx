import React, { useState } from "react"
import { TouchableOpacity, Text, StyleSheet } from "react-native"
import { TimerIcon, WarningIcon } from "../../../components/SvgAssets/SvgAssets"
import Tooltip from "react-native-walkthrough-tooltip";
import { colors } from "../../../config/constants";

export const TallyTrainingIcon = (props) => {
  const [isVisible, setIsVisible] = useState(false);

  const tallyContent = () => {
    const state = props.state;
    const hasPartCert = props.hasPartCert;

    if(['P.offer', 'P.draft'].includes(state)) {
      return warning;
    } else if(state === 'H.offer') {
      return timer;
    }

    return null;
  }
  const onPress = () => {
    setIsVisible(!isVisible);
  }

  if (tallyContent()) {
    return <Tooltip
      isVisible={isVisible}
      content={
        <Text>{tallyContent().message}</Text>
      }
      placement="top"
      onClose={onPress}
      contentStyle={[styles.contentStyle]}
      tooltipStyle={{}}
      childrenWrapperStyle={{ opacity: 0 }}
    // backgroundColor="transparent"
    >
      <TouchableOpacity style={[styles.touchable, props.style]} onPress={onPress}>
        {tallyContent().icon}
      </TouchableOpacity>
    </Tooltip >
  }
  return <></>
}

const styles = StyleSheet.create({
  contentStyle: {
    maxWidth: 200,
  },
  touchable: {
    top:-5,
    right:-25,
    position:'absolute',
  }
});

const warning = { icon: <WarningIcon size={16} color={colors.red}/>, message: "Your prospective partner is waiting for you to act on this tally" };
const timer = { icon: <TimerIcon size={16} />, message: "You are waiting on someone else before the tally is complete" }

