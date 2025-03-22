/**
 * Centralized crypto service for the MyCHIPs app
 * Provides access to cryptographic functionality using QuickCrypto
 */
import QuickCrypto from 'react-native-quick-crypto';
import { Buffer } from '@craftzdog/react-native-buffer';
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
export const deriveKey = async (password, salt) => {
  try {
    const subtle = getSubtle();
    
    // Generate a random salt if not provided
    const useSalt = salt || crypto.getRandomValues(new Uint8Array(8));
    
    // Import the password as a key
    const importedKey = await subtle.importKey(
      "raw", 
      Buffer.from(password), 
      { name: "PBKDF2" }, 
      false, 
      ["deriveKey"]
    );
    
    // Derive the key
    const key = await subtle.deriveKey(
      { name: "PBKDF2", salt: useSalt, iterations: 10000, hash: "SHA-256" },
      importedKey,
      { name: 'AES-GCM', length: 256 },
      true,
      ["encrypt", "decrypt"],
    );
    
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
    const subtle = getSubtle();
    
    // Generate a random IV if not provided
    const useIv = iv || crypto.getRandomValues(new Uint8Array(12));
    
    // Convert string data to buffer if needed
    const dataBuffer = typeof data === 'string' ? Buffer.from(data) : data;
    
    // Encrypt the data
    const ciphertext = await subtle.encrypt(
      { name: "AES-GCM", iv: useIv },
      key,
      dataBuffer
    );
    
    return { ciphertext, iv: useIv };
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
    const subtle = getSubtle();
    
    // Decrypt the data
    return subtle.decrypt(
      { name: "AES-GCM", iv },
      key,
      ciphertext
    );
  } catch (error) {
    console.error('Error decrypting data:', error);
    throw error;
  }
};

/**
 * Sign data using the private key
 * @param {ArrayBuffer} data - The data to sign
 * @param {CryptoKey} privateKey - The private key to use
 * @param {Object} algorithm - The algorithm to use
 * @returns {Promise<ArrayBuffer>} - The signature
 */
export const sign = async (data, privateKey, algorithm) => {
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