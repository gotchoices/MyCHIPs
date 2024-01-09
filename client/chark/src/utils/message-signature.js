import { TextEncoder } from 'web-encoding';
import { Buffer } from "buffer";

import { retrieveKey } from "./keychain-store";
import { keyServices, KeyConfig } from "../config/constants";

const subtle = window.crypto.subtle;

function base64ToBase64url(base64) {
  return base64
    .replace(/\+/g, '-')
    .replace(/\//g, '_');
}


export const createSignature = (message) => {
  return new Promise(async (resolve, reject) => {
    try {
      const encoder = new TextEncoder();
      const data = encoder.encode(message);
      retrieveKey(keyServices.privateKey)
        .then(creds => {
          if (creds) {
            console.log("PRIVATE KEY ==> ", creds.password);
            return subtle.importKey('jwk', JSON.parse(creds.password), KeyConfig, true, ['sign']);
          } else {
            throw { isKeyAvailable: false, message: "Create Keys!" };
          }
        })
        .then(pvtKey => subtle.sign(KeyConfig, pvtKey, data))
        .then(signature => Buffer.from(signature).toString('base64'))
        .then(base64 => resolve(base64ToBase64url(base64)))
        .catch(ex => reject(ex));
    } catch (ex) {
      reject(ex);
    }
  });
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

