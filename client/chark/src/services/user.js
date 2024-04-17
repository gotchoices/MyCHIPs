
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

  return request(wm, `chip_json_${random()}`, 'action', spec);
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

export const getUserCert = (wm) => {
  const spec = {
    fields: ['user_ent', 'cert'],
    view: 'mychips.users_v_me',
  }

  return request(wm, `_user_ref_${random()}`, 'select', spec).then(response => {
    return response?.[0]?.cert;
  })
}
