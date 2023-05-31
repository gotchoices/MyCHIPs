import { random } from '../utils/common';
import { langRegister, request } from './request';

export const getTallyText = (wm) => {
  return langRegister(wm, '_tally_lang' + random(), 'mychips.tallies');
}

/**
 * @param {Object} - args
 * @param {string[]} - args.fields
 * @param {any} - [args.where]
 */
export const fetchTallies = (wm, args) => {
  const spec = {
    fields: args.fields,
    view: 'mychips.tallies_v_me',
  }

  if(args.where) {
    spec.where = where;
  }

  return request(wm, 'tallies' + random(), 'select', spec);
}

