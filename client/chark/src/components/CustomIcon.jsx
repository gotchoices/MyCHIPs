import React from 'react';
import { View, TouchableOpacity } from 'react-native';
import Icon from 'react-native-vector-icons/Ionicons';
import ICReceive from '../../assets/svg/ic_chit_receive.svg';
import ICSettings from '../../assets/svg/ic_setting.svg';
import ICScan from '../../assets/svg/ic_scanner.svg';
import ICInvite from '../../assets/svg/ic_invite.svg';
import ICHome from '../../assets/svg/ic_home.svg';
import { IconWrapper } from './SvgAssets/SvgAssets';


const getIconName = (name) => {
  switch (name) {
    default: return name
  }
}

export default function CustomIcon(props) {
  const iconName = props.name;

  if (icons.hasOwnProperty(iconName)) {
    const icon = icons[iconName]({ ...props });

    if (props.onPress) {
      return (
        <TouchableOpacity {...props}>
          {icon}
        </TouchableOpacity>
      )
    } else {
      return (
        <View {...props}>
          {icon}
        </View >
      )
    }
  } else {
    return (
      <Icon {...props} name={iconName} />
    )
  }
}

const icons = {
  "home": (args) => <IconWrapper IconComponent={ICHome} {...args} />,
  "receive": (args) => <IconWrapper IconComponent={ICReceive} {...args} />,
  "scan": (args) => <IconWrapper IconComponent={ICScan} {...args} />,
  "invite": (args) => <IconWrapper IconComponent={ICInvite} {...args} />,
  "settings": (args) => <IconWrapper IconComponent={ICSettings} {...args} />,
}