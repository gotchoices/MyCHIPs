import { random } from '../utils/common';
import { langRegister, request } from './request';

export const getTallyText = (wm) => {
  return langRegister(wm, '_tally_lang' + random(), 'mychips.tallies');
}

/**
 * @param {Object} args
 * @param {string[]} args.fields
 * @param {any} [args.where]
 * @param {any} [args.order]
 */
export const fetchTallies = (wm, args) => {
  const spec = {
    fields: args.fields,
    view: 'mychips.tallies_v_me',
  }

  if (args.where) {
    spec.where = args.where;
  }

  if (args.order) {
    spec.order= args.order;
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

export const insertChit = (wm, payload) => {
  const spec = {
    fields: payload,
    view: 'mychips.chits_v_me',
  };

  return request(wm, '_chit_insert' + random(), 'insert', spec);
}

export const updateChitState = (wm, args) => {
  const data = {
    request: args.request,
  };

  const spec = {
    fields: data,
    view: 'mychips.chits_v_me',
    where: {
      chit_uuid: args.chit_uuid,
    },
  }

  return request(wm, '_chit_refuse' + random(), 'update', spec)
}

export const updateChitDetails = (wm, args) => {
  const data = args?.data;

  const spec = {
    fields: data,
    view: 'mychips.chits_v_me',
    where: {
      chit_ent: args?.chit_ent,
      chit_idx: args?.chit_idx,
      chit_seq: args?.chit_seq,
      chit_uuid: args?.chit_uuid,
    },
  }

  return request(wm, '_chit_refuse' + random(), 'update', spec)
}

/**
 * @param {Object} - args
 * @param {string[]} - args.tally_uuid
 * @param {string[]} - args.tally_ent
 * @param {string[]} - args.tally_seq
 * @param {string[]} - args.signature
 */
export const offerTally = (wm, args) => {
  const fields = {
    tally_uuid: args.tally_uuid,
    request: 'offer',
    hold_sig: args.signature,
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
 * @param {string} - args.signature
 */
export const acceptTally = (wm, args) => {
  const fields = {
    request: 'open',
    hold_sig: args.signature,
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

export const fetchTallyFile = (wm, digest, tally_seq) => {
  const spec = {
    name: 'file',
    view: 'mychips.tallies_v_me',
    data: {
      key: {
        tally_seq,
      },
      options: {
        digest,
        format: 'json',
      }
    }
  }

  return request(wm, 'fetch_tally_file' + random(1000), 'action', spec);
}

/**
 * @param {Object} args - Argument
 * @param {Object} args.wm - Wyseman instance
 * @param {any} args.payload - payload for action
 * @param {number} args.payload.tally_seq - payload for action
 */
export const fetchTradingVariables = (wm, payload) => {
  const spec = {
    name: 'trade',
    view: 'mychips.tallies_v_me',
    data: {
      key: payload.tally_seq,
      options: {
        format: 'url',
      }
    }
  }

  return request(wm, 'fetch_trade' + random(1000), 'action', spec);
}

/**
 * @param {Object} args
 * @param {string[]} args.fields
 * @param {any} [args.where]
 */
export const fetchContracts = (wm, args) => {
  const spec = {
    fields: args.fields,
    view: 'mychips.contracts_v',
  }

  if (args.where) {
    spec.where = args.where;
  }

  return request(wm, 'contracts' + random(), 'select', spec);
}

/**
 * @param {Object} args
 * @param {string[]} args.tally_seq
 */
export const getContract = (wm, args) => {
  const spec = {
    name: 'agree',
    view: 'mychips.tallies_v_me',
    data: {
      key: {
        tally_seq: args.tally_seq,
      },
      options: {
        format: 'url'
      }
    },
  };

  return request(wm, 'agree' + random(), 'action', spec);
}


export const updateHoldCert = (wm, args) => {
  const fields = {
    hold_cert: args.hold_cert,
  };

  const spec = {
    fields,
    view: 'mychips.tallies_v_me',
    where: {
      tally_ent: args.tally_ent,
      tally_seq: args.tally_seq,
    },
  }

  console.log("MY_REQUEST ==> ", JSON.stringify(spec));

  return request(wm, '_update_hold_cert_' + random(), 'update', spec);
}

/**
 * @param {Object} - args
 * @param {string[]} - args.tally_ent
 * @param {string[]} - args.tally_seq
 */
export const reviseTally = (wm, args) => {
  const fields = {
    request: 'draft',
  };

  const spec = {
    fields,
    view: 'mychips.tallies_v_me',
    where: {
      tally_ent: args.tally_ent,
      tally_seq: args.tally_seq,
    },
  }

  return request(wm, '_tally_revise' + random(), 'update', spec)
}

/**
 * @param {Object} - args
 * @param {string[]} - args.data
 */
export const processTicket = (wm, ticketPayload) => {
  const spec = {
    view: 'mychips.ticket_process',
    params: [ticketPayload],
  }

  return request(wm, '_process_tally' + random(), 'select', spec);
}

export const getHolderImage = (wm, digest) => {
  const spec = {
    fields: ['file_ent', 'file_fmt', 'file_data64'],
    view: 'mychips.file_v_me',
    where: {
      digest: digest,
    },
  }

  return request(wm, 'holder_image' + random(1000), 'select', spec).then((data) => {
    if(data?.[0]) {
      data[0].digest = digest;
      return data;
    }
  });
}
