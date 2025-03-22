import { TextEncoder } from 'web-encoding';
import { Buffer } from "buffer";

import { retrieveKey } from "./keychain-store";
import { keyServices, KeyConfig } from "../config/constants";
import { KeyNotFoundError } from '../utils/Errors';
import { importKey, sign, getSubtle } from '../services/crypto';

function base64ToBase64url(base64) {
  return base64
    .replace(/\+/g, '-')
    .replace(/\//g, '_');
}


export const createSignature = async (message) => {
  try {
    const encoder = new TextEncoder();
    const data = encoder.encode(message);
    const creds = await retrieveKey(keyServices.privateKey);

    if (creds) {
      // Use the crypto service for key import and signing
      const pvtKey = await importKey('jwk', JSON.parse(creds.password), KeyConfig, true, ['sign']);
      const signature = await sign(KeyConfig, pvtKey, data);
      const base64 = Buffer.from(signature).toString('base64');
      return base64ToBase64url(base64);
    } else {
      throw new KeyNotFoundError('Private key not found');
    }
  } catch (err) {
    console.error('Error creating signature:', err);
    throw err;
  }
}

export const verifySignature = (signature, message, publicKey) => {
  return new Promise(async (resolve, reject) => {
    try {
      const rawSignature = Buffer.from(signature, 'base64');
      const rawData = Buffer.from(message);
      
      // Use the crypto service for key import and verification
      importKey('jwk', JSON.parse(publicKey), KeyConfig, true, ['verify'])
        .then(key => {
          // Get subtle from the service and use it to verify
          const subtle = getSubtle();
          return subtle.verify(KeyConfig, key, rawSignature, rawData);
        })
        .then(verified => resolve(verified))
        .catch(ex => {
          console.error('Error verifying signature:', ex);
          reject(ex);
        });
    } catch (ex) {
      console.error('Exception in verifySignature:', ex);
      reject(ex);
    }
  });
}

