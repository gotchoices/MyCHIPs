import React from 'react';
import ICScannner from '../../../assets/svg/ic_scanner.svg';
import ICHome from '../../../assets/svg/ic_home.svg';
import ICChitReceive from '../../../assets/svg/ic_chit_receive.svg';
import ICInvite from '../../../assets/svg/ic_invite.svg';
import ICSetting from '../../../assets/svg/ic_setting.svg';
import ICChit from '../../../assets/svg/ic_chit.svg';
import ICVisual from '../../../assets/svg/ic_visual.svg';
import ICTabular from '../../../assets/svg/ic_tabular.svg';
import ICFilter from '../../../assets/svg/ic_filter.svg';
import ICSearch from '../../../assets/svg/ic_search.svg';
import IMGProfile from '../../../assets/svg/img_profile.svg';
import ICFilterSecond from '../../../assets/svg/ic_filter_second.svg';
import ICArrowBackward from '../../../assets/svg/ic_arrow_backward.svg';
import ICArrowForward from '../../../assets/svg/ic_arrow_forward.svg';
import ICAdd from '../../../assets/svg/ic_add.svg';
import ICWarning from '../../../assets/svg/ic_warning.svg';
import ICTimer from '../../../assets/svg/ic_timer.svg';
import ICSwitchKey from '../../../assets/svg/ic_switch_key.svg';
import ICSwitchSelected from '../../../assets/svg/ic_switch_selected.svg';
import ICSwithUnselected from '../../../assets/svg/ic_switch_unselected.svg';
import ICSelected from '../../../assets/svg/ic_selected.svg';
import ICUnselected from '../../../assets/svg/ic_unselected.svg';
import { colors } from '../../config/constants';


export const SelectedIcon = () => <ICSelected />

export const UnSelectedIcon = () => <ICUnselected />

export const SwithcKeyIcon = () => <ICSwitchKey />

export const SwitchSelectedIcon = () => <ICSwitchSelected />

export const SwitchUnselectedIcon = () => <ICSwithUnselected />

export const IconWrapper = ({ IconComponent, color, size }) => {
  const iconProps = {
    color: color || colors.black100,
    ...(size && { height: size }),
    ...(size && { width: size }),
  };
  return <IconComponent {...iconProps} />;
};

export const TimerIcon = ({ size, color }) => <ICTimer height={size ?? 11} width={size ?? 9} color={color ?? "#ADADAD"} />

export const WarningIcon = ({ size, color }) => <ICWarning height={size ?? 9} width={size ?? 9} color={color ?? "#E77A71"} />

export const AddIcon = ({ size, color }) => <ICAdd height={size ?? 24} width={size ?? 24} color={color ?? colors.white} />

export const ArrowBackwardIcon = ({ color }) => <ICArrowBackward color={color ?? "#EAEAEA"} />

export const ArrowForwardIcon = ({ color }) => <ICArrowForward color={color ?? "#EAEAEA"} />

export const VisualIcon = () => <ICVisual />

export const SearchIcon = ({ size }) => <ICSearch height={size ?? 18} width={size ?? 18} />

export const TabularIcon = () => <ICTabular />

export const FilterIcon = ({ size, color }) => <ICFilter height={size ?? 12} width={size ?? 18} color={color ?? "#344054"} />

export const FilterSecondIcon = () => <ICFilterSecond />

export const ProfileImage = ({ size }) => {
  return <IMGProfile height={size} width={size} />
}

export const ChitIcon = (props) => {
  return <ICChit
    color={props.color ?? colors.green}
    height={props.height ?? 32}
    width={props.width ?? 18}
  />
}

export const SettingIcon = (props) => {
  return <ICSetting
    color={props.color ?? colors.black100}
  />
}

export const InviteIcon = (props) => {
  return <ICInvite
    color={props.color ?? colors.black100}
  />
}

export const ChitReceiveIcon = (props) => {
  return <ICChitReceive
    color={props.color ?? colors.black100}
  />
}

export const HomeIcon = (props) => {
  return <ICHome
    color={props.color ?? colors.black100}
  />
}

export const ScannerIcon = (props) => {
  return <ICScannner
    color={props.color ?? colors.black100}
  />
}