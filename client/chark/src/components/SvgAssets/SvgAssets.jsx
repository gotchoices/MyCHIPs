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
import { colors } from '../../config/constants';


export const VisualIcon = () => <ICVisual />

export const SearchIcon = () => <ICSearch />

export const TabularIcon = () => <ICTabular />

export const FilterIcon = () => <ICFilter />


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