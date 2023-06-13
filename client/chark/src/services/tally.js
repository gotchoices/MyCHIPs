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

  if (args.where) {
    spec.where = args.where;
  }

  return request(wm, 'tallies' + random(), 'select', spec);
}

export const fetchChitHistory = (wm, args) => {
  const spec = {
    fields: args.fields,
    view: 'mychips.chits_v_me',
  };

  if (args.order) {
    spec.order = args.order;
  }

  if (args.where) {
    spec.where = args.where;
  }
  return request(wm, '_chit_history' + random(), 'select', spec);
}

/**
 * @param {Object} - args
 * @param {string[]} - args.tally_uuid
 * @param {string[]} - args.tally_ent
 * @param {string[]} - args.tally_seq
 */
export const offerTally = (wm, args) => {
  const fields = {
    tally_uuid: args.tally_uuid,
    request: 'offer',
    hold_sig: 'Originator Signature',
  };

  const spec = {
    fields,
    view: 'mychips.tallies_v_me',
    where: {
      tally_ent: args.tally_ent,
      tally_seq: args.tally_seq,
    },
  }

  return request(wm, '_tally_offer' + random(), 'update', spec)
}

/**
 * @param {Object} - args
 * @param {string[]} - args.tally_ent
 * @param {string[]} - args.tally_seq
 */
export const acceptTally = (wm, args) => {
  const fields = {
    request: 'open',
    hold_sig: 'Subject Signature',
  };

  const spec = {
    fields,
    view: 'mychips.tallies_v_me',
    where: {
      tally_ent: args.tally_ent,
      tally_seq: args.tally_seq,
    },
  }

  return request(wm, '_tally_accept' + random(), 'update', spec)
}

export const refuseTally = (wm, args) => {
  const data = {
    request: 'void',
    hold_sig: null,
  };

  const spec = {
    fields: data,
    view: 'mychips.tallies_v_me',
    where: {
      tally_ent: args.tally_ent,
      tally_seq: args.tally_seq,
    },
  }

  return request(wm, '_tally_reject' + random(), 'update', spec)
}

export const createTemplate = (wm, payload) => {
  const spec = {
    fields: payload,
    view: 'mychips.tallies_v_me',
  }

  return request(wm, 'new_template' + random(1000), 'insert', spec)
}
