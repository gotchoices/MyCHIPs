import React from "react";
import {
  View,
} from "react-native";
import { useSelector } from "react-redux";

import UnreadIcon from '../../../assets/svg/ic_unread.svg'
import { NotificationIcon, } from "../../components/SvgAssets/SvgAssets";

const Notification = () => {
  const { hasNotification } = useSelector((state) => state.activity);

  return (
    <View>
      {hasNotification && <UnreadIcon style={{ position: 'absolute', zIndex: 1, left: -7, top: -4 }} /> }
      <NotificationIcon />
    </View>
  )
}

export default Notification;
