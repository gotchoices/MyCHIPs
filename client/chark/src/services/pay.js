import { random } from '../utils/common';
import { request } from './request';

/**
 * @param {Object} args
 * @param {any} args.wm
 * @param {Object} args.payload
 */
export const createLiftsPay = (wm, payload) => {
  const {
    memo,
    ref, 
    chad,
    units = 0,
  } = payload;

  const [cid, agent] = chad?.split(":");
  const sign = 'Signature';

  const auth = { memo, ref, sign };
  const _units = parseInt(units) * 1000;
  const find = { cid, agent }

  const spec = {
    fields: {
      find,
      units: _units,
      payor_auth: auth,
      request: 'init',
    },
    view: 'mychips.lifts_v_pay_me',
  };

  return request(wm, 'lifts_v_pay_me' + random(), 'insert', spec);
}
