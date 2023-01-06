import { random } from '../utils/common';

export const request = (wm, uniqueId, action, spec) => {
  return new Promise((resolve) => {
    wm.request(uniqueId, action, spec, (data) => {
      resolve(data);
    })
  })
}

export const getComm = (wm, user_ent) => {
  const spec = {
    fields: ['comm_type', 'comm_spec', 'comm_seq', 'comm_prim'],
    view: 'mychips.comm_v_me',
    where: {
      comm_ent: user_ent,
    },
    order: {
      field: 'crt_date',
      asc: true,
    }
  }

  return request(wm, '_comm_ref', 'select', spec);
}

export const getPersonal = (wm, user_ent) => {
  const spec = {
    fields: ['user_ent', 'tax_id', 'born_date', 'country', 'cas_name'],
    view: 'mychips.users_v_me',
    where: {
      user_ent,
    }
  }


  return request(wm, `_user_ref_${random(1000)}`, 'select', spec).then(response => {
    const user = response?.[0];
    return {
      born_date: user?.born_date ?? '',
      country: user?.country ?? '',
      tax_id: user?.tax_id ?? '',
      cas_name: user?.cas_name ?? '',
    }
  });
}

export const getAddresses = (wm, user_ent) => {
  const spec = {
    fields: ['addr_ent', 'addr_spec', 'addr_seq', 'addr_type', 'city', 'state', 'country', 'pcode'],
    view: 'mychips.addr_v_me',
    where: {
      addr_ent: user_ent,
    },
    order: {
      field: 'crt_date',
      asc: true,
    }
  };

  return request(wm, '_addr_ref' + random(1000), 'select', spec);
}

const langRegister = (wm, uniqueId, view) => {
  return new Promise((resolve) => {
    wm.register(uniqueId, view, (data, err) => {
      if (err) {
        resolve({})
      }

      resolve(data?.col ?? {});
    })
  })
}

export const getLang = (wm) => {
  const addr = langRegister(wm, '_addr_lang', 'base.addr_v_flat').then();
  const comm = langRegister(wm, '_comm_lang', 'base.comm_v_flat');
  const personal = langRegister(wm, 'user_lang', 'mychips.users_v_me');

  return Promise.all([
    addr,
    comm,
    personal,
  ]).then(responses => {

    const result = responses.reduce((response, acc) => {
      return Object.assign(acc, response ?? {});
    }, {});

    return result;
  })
}

export default request;
