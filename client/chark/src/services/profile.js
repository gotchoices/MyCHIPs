import { random } from '../utils/common';

export const request = (wm, uniqueId, action, spec) => {
  return new Promise((resolve, reject) => {
    wm.request(uniqueId, action, spec, (data, err) => {
      if (err) {
        return reject(err)
      }
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
      asc: false,
    }
  }

  return request(wm, '_comm_ref' + random(), 'select', spec);
}

export const getPersonal = (wm, user_ent) => {
  const spec = {
    fields: ['user_ent', 'tax_id', 'born_date', 'country', 'cas_name', "peer_cuid", 'cert', 'ent_type', 'ent_name'],
    view: 'mychips.users_v_me',
    where: {
      user_ent,
    }
  }


  return request(wm, `_user_ref_${random()}`, 'select', spec).then(response => {
    const user = response?.[0];
    return {
      born_date: user?.born_date ?? '',
      country: user?.country ?? '',
      tax_id: user?.tax_id ?? '',
      cas_name: user?.ent_type === 'p' ? user?.cas_name : user?.ent_name ?? '',
      cuid: user?.peer_cuid ?? '',
      user_id: user?.user_ent ?? '',
      cert: user?.cert,
    }
  });
}

export const getUserCert = (wm, user_ent) => {
  const spec = {
    view: 'mychips.user_cert',
    params: [user_ent]
  };

  return request(wm, `_user_cert_${random()}`, 'select', spec);
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

  return request(wm, '_addr_ref' + random(), 'select', spec);
}


export const getCountry = (wm, co_code) => {
  const spec = {
    fields: ['cur_code', 'co_name', 'co_code'],
    view: 'base.country_v',
    where: {
      co_code,
    }
  };

  return request(wm, '_co_ref' + random(), 'select', spec).then((countries) => {
    return countries?.[0];
  })
}


export const getCurrency = (wm, cur_code) => {
  const spec = {
    fields: ['cur_name', 'cur_code'],
    view: 'base.currency',
    where: {
      cur_code,
    }
  }

  return request(wm, '_cur_ref' + random(), 'select', spec).then(currencies => {
    return currencies?.[0];
  });
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

export const getProfileText = (wm) => {
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

export const uploadImage = (wm, payload) => {
  const spec = {
    name: 'photo',
    view: 'mychips.file_v_me',
    data: {
      fields: payload,
    },
  }

  return request(wm, 'upload_image' + random(), 'action', spec);
}

export const getFile = (wm, user_ent) => {
  const spec = {
    fields: ['file_ent', 'file_fmt', 'file_data64'],
    view: 'mychips.file_v_me',
    where: {
      file_ent: user_ent,
      file_prim: true,
    },
  }

  return request(wm, 'get_image' + random(), 'select', spec);
}

export const updateCUID = (wm, args) => {
  const fields = {
    peer_cuid: args.peer_cuid
  }
  const spec = {
    fields,
    view: "mychips.users_v_me"
  }

  if (args.where) {
    spec.where = args.where
  }
  return request(wm, "_update_cuid" + random(), 'update', spec);
}

export const updatePublicKey = (wm, args) => {
  const fields = {
    user_psig: args.public_key,
  }
  const spec = {
    fields,
    view: 'mychips.users_v_me',
  }
  if (args.where) {
    spec.where = args.where;
  }
  return request(wm, "_update_key" + random(), 'update', spec);
}

export default request;
