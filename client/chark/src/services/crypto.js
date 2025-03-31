/**
 * Centralized crypto service for the MyCHIPs app
 * Provides access to cryptographic functionality using QuickCrypto
 */
import QuickCrypto from 'react-native-quick-crypto';
import { Buffer } from 'buffer';
import 'react-native-get-random-values';

// Ensure the crypto service is initialized
let isInitialized = false;

/**
 * Initialize the crypto service
 * This should be called early in the app lifecycle (e.g., in App.js)
 */
export const initCryptoService = () => {
  if (!isInitialized) {
    // Set up global Buffer
    if (!global.Buffer) {
      global.Buffer = Buffer;
    }
    
    // Install QuickCrypto
    QuickCrypto.install();
    
    isInitialized = true;
    console.log('Crypto service initialized');
  }
};

/**
 * Get the Web Crypto API's subtle interface
 * This ensures consistent access to the crypto functionality across the app
 */
export const getSubtle = () => {
  // Make sure the service is initialized
  if (!isInitialized) {
    initCryptoService();
  }
  
  // Try to access the subtle API
  const subtle = window.crypto?.subtle || global.crypto?.subtle;
  
  if (!subtle) {
    console.error('Failed to get Web Crypto subtle API');
    throw new Error('Web Crypto API not available');
  }
  
  return subtle;
};

/**
 * Generate random values (replacement for crypto.getRandomValues)
 * @param {TypedArray} array - The array to fill with random values
 * @returns {TypedArray} - The array filled with random values
 */
export const getRandomValues = (array) => {
  // Make sure the service is initialized
  if (!isInitialized) {
    initCryptoService();
  }
  
  // Use QuickCrypto's getRandomValues function
  return QuickCrypto.getRandomValues(array);
};

/**
 * Generate a random key pair for signing
 * @param {Object} config - Key configuration
 * @param {Array} usage - Key usage array (e.g., ['sign', 'verify'])
 * @returns {Promise<Object>} - The generated key pair
 */
export const generateKeyPair = async (config, usage = ['sign', 'verify']) => {
  const subtle = getSubtle();
  return subtle.generateKey(config, true, usage);
};

/**
 * Export a key to the specified format
 * @param {string} format - The format to export to (e.g., 'jwk')
 * @param {CryptoKey} key - The key to export
 * @returns {Promise<Object>} - The exported key
 */
export const exportKey = async (format, key) => {
  const subtle = getSubtle();
  return subtle.exportKey(format, key);
};

/**
 * Import a key from the specified format
 * @param {string} format - The format to import from (e.g., 'jwk')
 * @param {Object} key - The key data to import
 * @param {Object} algorithm - The algorithm to use
 * @param {boolean} extractable - Whether the key should be extractable
 * @param {Array} usage - The key usage array
 * @returns {Promise<CryptoKey>} - The imported key
 */
export const importKey = async (format, key, algorithm, extractable, usage) => {
  const subtle = getSubtle();
  return subtle.importKey(format, key, algorithm, extractable, usage);
};

/**
 * Derive a key from a password and salt
 * @param {string} password - The password to derive from
 * @param {Uint8Array} [salt] - The salt to use (generated if not provided)
 * @returns {Promise<Array>} - [derivedKey, salt]
 */
export const derivePassKey = async (password, salt) => {
  try {
    // Generate a random salt if not provided
    const useSalt = salt || getRandomValues(new Uint8Array(8));
    
    // Use QuickCrypto's pbkdf2Sync to derive key material
    const keyMaterial = QuickCrypto.pbkdf2Sync(
      Buffer.from(password),
      useSalt,
      10000,
      32, // 256 bits
      'sha256'
    );
    
    // Create a CryptoKey-compatible object that works with encrypt/decrypt
    const key = {
      type: 'secret',
      algorithm: { name: 'AES-GCM', length: 256 },
      extractable: true,
      usages: ['encrypt', 'decrypt'],
      
      // Store key material for use in encrypt/decrypt
      _keyMaterial: keyMaterial,
      
      // Custom toString to help with debugging
      toString: function() {
        return '[object CryptoKey]';
      }
    };
    
    return [key, useSalt];
  } catch (error) {
    console.error('Error deriving key:', error);
    throw error;
  }
};

/**
 * Encrypt data using AES-GCM
 * @param {string|ArrayBuffer} data - The data to encrypt
 * @param {CryptoKey} key - The key to use
 * @param {Uint8Array} [iv] - The initialization vector (generated if not provided)
 * @returns {Promise<Object>} - { ciphertext, iv }
 */
export const encrypt = async (data, key, iv) => {
  try {
    // Check if this is our custom key or a WebCrypto key
    if (key._keyMaterial) {
      // This is our custom key, use QuickCrypto directly
      
      // Generate a random IV if not provided
      const useIv = iv || getRandomValues(new Uint8Array(12));
      
      // Convert string data to buffer if needed
      const dataBuffer = typeof data === 'string' ? Buffer.from(data) : data;
      
      // Use QuickCrypto's createCipheriv for encryption
      const cipher = QuickCrypto.createCipheriv('aes-256-gcm', key._keyMaterial, useIv);
      let encrypted = cipher.update(dataBuffer);
      encrypted = Buffer.concat([encrypted, cipher.final()]);
      
      // Get the authentication tag
      const authTag = cipher.getAuthTag();
      
      // Combine the encrypted data and authentication tag
      const ciphertext = Buffer.concat([encrypted, authTag]);
      
      return { ciphertext, iv: useIv };
    } else {
      // This is a WebCrypto key, use the subtle interface
      const subtle = getSubtle();
      
      // Generate a random IV if not provided
      const useIv = iv || getRandomValues(new Uint8Array(12));
      
      // Convert string data to buffer if needed
      const dataBuffer = typeof data === 'string' ? Buffer.from(data) : data;
      
      // Encrypt the data
      const ciphertext = await subtle.encrypt(
        { name: "AES-GCM", iv: useIv },
        key,
        dataBuffer
      );
      
      return { ciphertext, iv: useIv };
    }
  } catch (error) {
    console.error('Error encrypting data:', error);
    throw error;
  }
};

/**
 * Decrypt data using AES-GCM
 * @param {ArrayBuffer} ciphertext - The encrypted data
 * @param {CryptoKey} key - The key to use
 * @param {Uint8Array} iv - The initialization vector
 * @returns {Promise<ArrayBuffer>} - The decrypted data
 */
export const decrypt = async (ciphertext, key, iv) => {
  try {
    // Check if this is our custom key or a WebCrypto key
    if (key._keyMaterial) {
      // This is our custom key, use QuickCrypto directly
      
      // Convert ciphertext to Buffer if needed
      const ciphertextBuffer = Buffer.isBuffer(ciphertext) ? ciphertext : Buffer.from(ciphertext);
      
      // AES-GCM uses the last 16 bytes as the authentication tag
      const authTagLength = 16;
      const encrypted = ciphertextBuffer.slice(0, ciphertextBuffer.length - authTagLength);
      const authTag = ciphertextBuffer.slice(ciphertextBuffer.length - authTagLength);
      
      // Use QuickCrypto's createDecipheriv for decryption
      const decipher = QuickCrypto.createDecipheriv('aes-256-gcm', key._keyMaterial, iv);
      decipher.setAuthTag(authTag);
      
      let decrypted = decipher.update(encrypted);
      decrypted = Buffer.concat([decrypted, decipher.final()]);
      
      return decrypted;
    } else {
      // This is a WebCrypto key, use the subtle interface
      const subtle = getSubtle();
      
      // Decrypt the data
      return subtle.decrypt(
        { name: "AES-GCM", iv },
        key,
        ciphertext
      );
    }
  } catch (error) {
    console.error('Error decrypting data:', error);
    throw error;
  }
};

/**
 * Sign data using the private key
 * @param {Object} algorithm - The algorithm to use
 * @param {CryptoKey} privateKey - The private key to use
 * @param {ArrayBuffer} data - The data to sign
 * @returns {Promise<ArrayBuffer>} - The signature
 */
export const sign = async (algorithm, privateKey, data) => {
  try {
    const subtle = getSubtle();
    return subtle.sign(algorithm, privateKey, data);
  } catch (error) {
    console.error('Error signing data:', error);
    throw error;
  }
};

// Initialize the service when imported
initCryptoService();