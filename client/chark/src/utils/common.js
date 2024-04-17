import 'react-native-get-random-values';
import { v4 as uuidv4 } from 'uuid';

export const round = (value, decimals) => {
  const temp = parseFloat(value + `e+${decimals}`);
  const result = Math.round(temp) + `e-${decimals}`;
  return parseFloat(result).toFixed(decimals);
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
