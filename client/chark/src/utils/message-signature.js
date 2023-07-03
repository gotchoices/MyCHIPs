import { KeyConfig, SignConfig } from "wyseman/lib/crypto";
import { retrieveKey } from "./keychain-store";
import { TextEncoder, TextDecoder } from 'web-encoding';
import { Buffer } from "buffer";
import PropTypes from 'prop-types';
import { keyServices } from "../config/constants";

const subtle = window.crypto.subtle;

export const createSignature = (message) => {
  return new Promise(async (resolve, reject) => {
    try {
      const encoder = new TextEncoder();
      const data = encoder.encode(message);
      retrieveKey(keyServices.privateKey)
        .then(creds => subtle.importKey('jwk', JSON.parse(creds.password), KeyConfig, true, ['sign']))
        .then(pvtKey => subtle.sign(SignConfig, pvtKey, data))
        .then(signature => resolve(Buffer.from(signature).toString('base64')))
        .catch(ex => reject(ex));
    } catch (ex) {
      reject(ex);
    }
  });
}
createSignature.prototype = {
  message: PropTypes.string.isRequired,
}

export const verifySignature = (signature, message, publicKey) => {
  return new Promise(async (resolve, reject) => {
    try {
      const rawSignature = Buffer.from(signature, 'base64');
      const rawData = Buffer.from(message);
      subtle.importKey('jwk', JSON.parse(publicKey), KeyConfig, true, ['verify'])
        .then(key => subtle.verify(SignConfig, key, rawSignature, rawData))
        .then(verified => resolve(verified))
        .catch(ex => reject(ex));
    } catch (ex) {
      reject(ex);
    }
  });
}

verifySignature.prototype = {
  signature: PropTypes.string.isRequired,
  message: PropTypes.string.isRequired,
  publicKey: PropTypes.string.isRequired,
}
