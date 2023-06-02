
import { request } from './request';
import { random } from '../utils/common';

export const getCurrency = (wm, curr) => {
  const spec = {
    name: 'chip',
    view: 'mychips.users_v_me',
    data: {
      options: {
        curr,
        format: 'json'
      }
    }
  };

  return request(wm, `chip_json_${random(1000)}`, 'action', spec);
}

export const getTallyReport = (wm) => {
  const spec = {
    name:'graph',
    view:'mychips.users_v_me',
    data: {
      options: {
        format: 'url'
      }
    }
  }

  return request(wm, `visual_balance_${random()}`, 'action', spec)
}
