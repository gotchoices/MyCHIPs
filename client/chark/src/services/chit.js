import { random } from '../utils/common';
import { request } from './request';

/**
 * @param {Object} args
 * @param {any} args.wm
 * @param {string[]} args.fields
 * @param {any} [args.where]
 * @param {any} [args.order]
 */
export const fetchChits = (wm, args) => {
  const spec = {
    fields: args.fields,
    view: 'mychips.chits_v_me',
  }

  if (args.where) {
    spec.where = args.where;
  }

  if (args.order) {
    spec.order= args.order;
  }

  return request(wm, 'chits' + random(), 'select', spec);
}

/**
 * @param {Object} args
 * @param {number} args.units
 * @param {any} args.memo
 * @param {any} args.format
 * @param {any=} args.ref
 */
export const receiveChit = (wm, args) => {
  const options = {
    units: args.units,
    memo: args.memo ?? '',
    format: args.format,
  }

  if(args.ref) {
    options.ref = args.ref;
  }

  const spec = {
    name: 'invoice',
    view: 'mychips.users_v_me', 
    data: {
      options,
    }
  }
  console.log(spec, 'spec')
  return request(wm, 'invoice' + random(), 'action', spec);
}

/**
 * @param {Object} args
 * @param {payload} args.payload
 */
export const insertChit = (wm, payload) => {
  const spec = {
    fields: payload,
    view: 'mychips.chits_v_me',
  };

  return request(wm, '_chit_insert' + random(), 'insert', spec);
}
