import React from "react";

import ICAdd from "../../../assets/svg/ic_add.svg";
import ICHome from "../../../assets/svg/ic_home.svg";
import ICChit from "../../../assets/svg/ic_chit.svg";
import ICShare from "../../../assets/svg/ic_share.svg";
import ICTimer from "../../../assets/svg/ic_timer.svg";
import ICInvite from "../../../assets/svg/ic_invite.svg";
import ICVisual from "../../../assets/svg/ic_visual.svg";
import ICFilter from "../../../assets/svg/ic_filter.svg";
import ICSearch from "../../../assets/svg/ic_search.svg";
import ICSetting from "../../../assets/svg/ic_setting.svg";
import ICTabular from "../../../assets/svg/ic_tabular.svg";
import ICWarning from "../../../assets/svg/ic_warning.svg";
import ICScannner from "../../../assets/svg/ic_scanner.svg";
import IMGProfile from "../../../assets/svg/img_profile.svg";
import ICSelected from "../../../assets/svg/ic_selected.svg";
import ICSwitchKey from "../../../assets/svg/ic_switch_key.svg";
import ICUnselected from "../../../assets/svg/ic_unselected.svg";
import ICChitReceive from "../../../assets/svg/ic_chit_receive.svg";
import ICFilterSecond from "../../../assets/svg/ic_filter_second.svg";
import ICArrowForward from "../../../assets/svg/ic_arrow_forward.svg";
import ICArrowBackward from "../../../assets/svg/ic_arrow_backward.svg";
import ICSwitchSelected from "../../../assets/svg/ic_switch_selected.svg";
import ICSwithUnselected from "../../../assets/svg/ic_switch_unselected.svg";

import ICSwap from "../../../assets/svg/swap.svg";
import ICUpArrow from "../../../assets/svg/ic_up_arrow.svg";
import ICDownArrow from "../../../assets/svg/ic_down_arrow.svg";
import ICLeftArrow from "../../../assets/svg/ic_left_arrow.svg";
import ICRightArrow from "../../../assets/svg/ic_right_arrow.svg";
import ICNotification from '../../../assets/svg/ic_notification.svg';

import { colors } from "../../config/constants";

export const SelectedIcon = () => <ICSelected />;

export const UnSelectedIcon = () => <ICUnselected />;

export const SwithcKeyIcon = () => <ICSwitchKey />;

export const SwitchSelectedIcon = () => <ICSwitchSelected />;

export const SwitchUnselectedIcon = () => <ICSwithUnselected />;

export const IconWrapper = ({ IconComponent, color, size }) => {
  const iconProps = {
    color: color || colors.black100,
    ...(size && { height: size }),
    ...(size && { width: size }),
  };
  return <IconComponent {...iconProps} />;
};

export const TimerIcon = ({ size, color }) => (
  <ICTimer height={size ?? 11} width={size ?? 9} color={color ?? "#ADADAD"} />
);

export const WarningIcon = ({ size, color }) => (
  <ICWarning height={size ?? 9} width={size ?? 9} color={color ?? "#E77A71"} />
);

export const AddIcon = ({ size, color }) => (
  <ICAdd height={size ?? 24} width={size ?? 24} color={color ?? colors.white} />
);

export const ArrowBackwardIcon = ({ color }) => (
  <ICArrowBackward color={color ?? "#EAEAEA"} />
);

export const ArrowForwardIcon = ({ color }) => (
  <ICArrowForward color={color ?? "#EAEAEA"} />
);

export const VisualIcon = () => <ICVisual color={colors.black} />

export const NotificationIcon = () => <ICNotification color={colors.black} />

export const SearchIcon = ({ size }) => (
  <ICSearch height={size ?? 18} width={size ?? 18} />
);

export const TabularIcon = () => <ICTabular />;

export const FilterIcon = ({ size, color }) => (
  <ICFilter height={size ?? 12} width={size ?? 18} color={color ?? "#344054"} />
);

export const FilterSecondIcon = () => <ICFilterSecond />;

export const ProfileImage = ({ size }) => {
  return <IMGProfile height={size} width={size} />;
};

export const ChitIcon = (props) => {
  return (
    <ICChit
      color={props.color ?? colors.green}
      height={props.height ?? 32}
      width={props.width ?? 18}
    />
  );
};

export const SettingIcon = (props) => {
  return <ICSetting color={props.color ?? colors.black100} />;
};

export const ShareIcon = (props) => {
  return (
    <ICShare
      height={props.size ?? 24}
      width={props.size ?? 24}
      color={props.color ?? colors.white}
    />
  );
};

export const InviteIcon = (props) => {
  return <ICInvite color={props.color ?? colors.black100} />;
};

export const ChitReceiveIcon = (props) => {
  return <ICChitReceive color={props.color ?? colors.black100} />;
};

export const HomeIcon = (props) => {
  return <ICHome color={props.color ?? colors.black100} />;
};

export const ScannerIcon = (props) => {
  return <ICScannner color={props.color ?? colors.black100} />;
};

export const LeftArrowIcon = (props) => {
  return <ICLeftArrow color={props.color ?? colors.black100} />;
};

export const RightArrowIcon = (props) => {
  return <ICRightArrow color={props.color ?? colors.black100} />;
};

export const UpArrowIcon = (props) => {
  return <ICUpArrow color={props.color ?? colors.black100} />;
};
export const DownArrowIcon = (props) => {
  return <ICDownArrow color={props.color ?? colors.black100} />;
};

export const SwapIcon = (props) => {
  return <ICSwap />;
};
