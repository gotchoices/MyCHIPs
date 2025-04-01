import { random, chipsToUnits } from '../utils/common';
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

  const [cuid, agent] = chad?.split(":");
  const sign = 'Signature';

  const auth = { memo, ref, sign };
  const _units = chipsToUnits(units);
  const find = { cuid, agent }

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
