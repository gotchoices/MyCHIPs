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

/**
 * @param {Object} - args
 * @param {string[]} - args.chit_ent
 * @param {string[]} - args.chit_uuid
 * @param {string} - args.signature
 */
export const acceptChit = (wm, args) => {
  const fields = {
    request: 'good',
    signature: args.signature,
  };

  const spec = {
    fields,
    view: 'mychips.chits_v_me',
    where: {
      chit_ent: args.chit_ent,
      chit_uuid: args.chit_uuid,
    },
  }

  return request(wm, 'accept_chit' + random(), 'update', spec)
}

/**
 * @param {any} - wm
 * @param {Object} - args
 * @param {string[]} - args.chit_ent
 * @param {string[]} - args.chit_uuid
 */
export const rejectChit = (wm, args) => {
  const fields = {
    request: 'void',
  };

  const spec = {
    fields,
    view: 'mychips.chits_v_me',
    where: {
      chit_ent: args.chit_ent,
      chit_uuid: args.chit_uuid,
    },
  }

  return request(wm, 'reject_chit' + random(), 'update', spec)
}
