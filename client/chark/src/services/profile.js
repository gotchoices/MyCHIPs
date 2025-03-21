/**
 * Profile-related API services for fetching and managing user profile data.
 * Provides functions to interact with backend Wyseman API for user data,
 * communications, address info, and file management.
 */

import { random } from '../utils/common';

/**
 * Core request function that wraps Wyseman API calls.
 * Handles connection issues gracefully with a non-resolving promise.
 * 
 * @param {Object} wm - Wyseman client instance
 * @param {string} uniqueId - Unique identifier for the request
 * @param {string} action - API action (select, update, etc.)
 * @param {Object} spec - Request specification
 * @returns {Promise} Promise that resolves with response data
 */
export const request = (wm, uniqueId, action, spec) => {
  // If wyseman isn't available, return a pending promise
  // This silently does nothing, matching the pattern elsewhere
  if (!wm) {
    return new Promise(() => {});
  }
  
  return new Promise((resolve, reject) => {
    wm.request(uniqueId, action, spec, (data, err) => {
      if (err) {
        return reject(err)
      }
      resolve(data);
    })
  })
}

/**
 * Fetches user communication methods (email, phone, etc.).
 * Orders results with newest first.
 * 
 * @param {Object} wm - Wyseman client instance
 * @param {string} user_ent - User entity ID
 * @returns {Promise<Array>} - Communication methods for the user
 */
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

/**
 * Fetches and formats personal user information.
 * Handles different entity types (personal vs organizational).
 * 
 * @param {Object} wm - Wyseman client instance
 * @param {string} user_ent - User entity ID
 * @returns {Promise<Object>} - Standardized user personal data
 */
export const getPersonal = (wm, user_ent) => {
  if (!user_ent) {
    // Return a non-resolving promise on missing user_ent
    return new Promise(() => {});
  }
  
  const spec = {
    fields: ['user_ent', 'tax_id', 'born_date', 'country', 'cas_name', "peer_cuid", 'cert', 'ent_type', 'ent_name'],
    view: 'mychips.users_v_me',
    where: {
      user_ent,
    }
  }

  return request(wm, `_user_ref_${random()}`, 'select', spec)
    .then(response => {
      const user = response?.[0];
      return {
        born_date: user?.born_date ?? '',
        country: user?.country ?? '',
        tax_id: user?.tax_id ?? '',
        cas_name: user?.ent_type === 'p' ? user?.cas_name : user?.ent_name ?? '',
        cuid: user?.peer_cuid ?? '',
        user_id: user?.user_ent ?? '',
        cert: user?.cert,
      };
    });
}

/**
 * Fetches user certificate information.
 * 
 * @param {Object} wm - Wyseman client instance
 * @param {string} user_ent - User entity ID
 * @returns {Promise<Array>} - User certificate data
 */
export const getUserCert = (wm, user_ent) => {
  const spec = {
    view: 'mychips.user_cert',
    params: [user_ent]
  };

  return request(wm, `_user_cert_${random()}`, 'select', spec);
}

/**
 * Fetches user address information.
 * Orders results with oldest first.
 * 
 * @param {Object} wm - Wyseman client instance
 * @param {string} user_ent - User entity ID
 * @returns {Promise<Array>} - Address records for user
 */
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

/**
 * Uploads user profile image.
 * 
 * @param {Object} wm - Wyseman client instance
 * @param {Object} payload - Image data payload with file information
 * @returns {Promise<Object>} - Result of the upload operation
 */
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

/**
 * Fetches primary image file for user (avatar).
 * Filters to only include primary image files.
 * 
 * @param {Object} wm - Wyseman client instance
 * @param {string} user_ent - User entity ID
 * @returns {Promise<Array>} - File data including base64-encoded content
 */
export const getFile = (wm, user_ent) => {
  if (!user_ent) {
    // Return a non-resolving promise on missing user_ent
    return new Promise(() => {});
  }
  
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
