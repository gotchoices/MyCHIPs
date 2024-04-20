import { TextEncoder } from 'web-encoding';
import { Buffer } from "buffer";

import { retrieveKey } from "./keychain-store";
import { keyServices, KeyConfig } from "../config/constants";
import { KeyNotFoundError } from '../utils/Errors';

const subtle = window.crypto.subtle;

function base64ToBase64url(base64) {
  return base64
    .replace(/\+/g, '-')
    .replace(/\//g, '_');
}


export const createSignature = async (message, ) => {
  try {
    const encoder = new TextEncoder();
    const data = encoder.encode(message);
    const creds = await retrieveKey(keyServices.privateKey)

    if (creds) {
      const pvtKey = await subtle.importKey('jwk', JSON.parse(creds.password), KeyConfig, true, ['sign']);
      const signature = await subtle.sign(KeyConfig, pvtKey, data)
      const base64 = Buffer.from(signature).toString('base64')
      return base64ToBase64url(base64)
    } else {
      throw new KeyNotFoundError('Create not found')
    }
  } catch (err) {
    throw err
  }
}

export const verifySignature = (signature, message, publicKey) => {
  return new Promise(async (resolve, reject) => {
    try {
      const rawSignature = Buffer.from(signature, 'base64');
      const rawData = Buffer.from(message);
      subtle.importKey('jwk', JSON.parse(publicKey), KeyConfig, true, ['verify'])
        .then(key => subtle.verify(KeyConfig, key, rawSignature, rawData))
        .then(verified => resolve(verified))
        .catch(ex => reject(ex));
    } catch (ex) {
      reject(ex);
    }
  });
}

