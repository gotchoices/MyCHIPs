
import { request } from './request';
import { random } from '../utils/common';

export const getCurrency = (wm) => {
  return request(wm, `currency_ref_${random()}`, 'select', {
    view: 'base.currency',
    fields: ['cur_code', 'cur_name'],
    order: {
      field: 'cur_name',
      asc: true,
    }
  });
}

