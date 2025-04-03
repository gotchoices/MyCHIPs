/**
 * Tally Verification Utilities
 * 
 * This module provides functions for validating the cryptographic integrity
 * of tallies, including signature verification.
 */

import stringify from 'json-stable-stringify';
import { verifySignature } from './message-signature';
import { retrieveKey } from './keychain-store';
import { keyServices } from '../config/constants';

/**
 * Validity status enum
 */
export const TallyValidityStatus = {
  VALID: 'valid',               // Tally is properly signed and verified
  WARNING: 'warning',           // Key mismatch or other non-critical issue
  INVALID: 'invalid',           // Invalid signature, missing key, unsigned, etc.
};

/**
 * Check if a tally should display a warning indicator
 * @param {string} status - The validity status
 * @returns {boolean} - True if a warning indicator should be shown
 */
export const needsWarningIndicator = (status) => {
  // Only show warning for INVALID or WARNING status
  // Don't show anything for undefined status (validation in progress)
  return status === TallyValidityStatus.INVALID || status === TallyValidityStatus.WARNING;
};

/**
 * Verify the signature of a tally
 * @param {Object} tally - The tally object containing json_core and hold_sig
 * @returns {Promise<boolean>} - True if signature is valid
 */
export const verifyTallySignature = async (tally) => {
  try {
    if (!tally?.json_core || !tally?.hold_sig) {
      return false;
    }

    // Create the message from the tally's json_core (same as when signing)
    const message = stringify(tally.json_core);
    
    // Get the public key from the holder's certificate
    const tallyType = tally?.tally_type; // 'foil' or 'stock'
    const holderPublicKey = tally?.json_core?.[tallyType]?.cert?.public;
    
    if (!holderPublicKey) {
      return false;
    }
    
    // Convert the key to a string if it's not already
    const keyString = typeof holderPublicKey === 'string' 
      ? holderPublicKey 
      : JSON.stringify(holderPublicKey);
    
    // Verify the signature
    return await verifySignature(tally.hold_sig, message, keyString);
  } catch (error) {
    console.error('Error verifying tally signature:', error);
    return false;
  }
};

/**
 * Check if the public key in a tally matches the user's current key
 * @param {Object} tally - The tally object containing the public key
 * @returns {Promise<boolean>} - True if keys match
 */
export const checkKeyMatch = async (tally) => {
  try {
    // Get the public key from the holder's certificate
    const tallyType = tally?.tally_type; // 'foil' or 'stock'
    const holderPublicKey = tally?.json_core?.[tallyType]?.cert?.public;
    
    if (!holderPublicKey) {
      return false;
    }
    
    const publicCreds = await retrieveKey(keyServices.publicKey);
    
    if (!publicCreds) {
      return false;
    }
    
    const currentPublicKey = JSON.parse(publicCreds.password);
    
    // Check if x and y coordinates match (EC keys)
    return currentPublicKey.x === holderPublicKey.x && currentPublicKey.y === holderPublicKey.y;
  } catch (error) {
    console.error('Error comparing public keys:', error);
    return false;
  }
};

/**
 * Get the validity status of a tally
 * @param {Object} tally - The tally object to check
 * @returns {Promise<string>} - The validity status from TallyValidityStatus enum
 */
export const getTallyValidityStatus = async (tally) => {
  try {
    if (!tally || !tally.json_core) {
      return TallyValidityStatus.INVALID;
    }
    
    // Get the public key from the holder's certificate
    const tallyType = tally?.tally_type; // 'foil' or 'stock'
    const hasPublicKey = !!tally?.json_core?.[tallyType]?.cert?.public;
    
    // If no public key or no signature, it's invalid
    if (!hasPublicKey || !tally.hold_sig) {
      return TallyValidityStatus.INVALID;
    }
    
    // Verify the signature
    const isSignatureValid = await verifyTallySignature(tally);
    
    if (!isSignatureValid) {
      return TallyValidityStatus.INVALID;
    }
    
    // Check if the key matches the user's current key
    const isKeyMatch = await checkKeyMatch(tally);
    
    // For the simple indicator, we just need to know:
    // - Valid: Good signature with matching key
    // - Warning: Good signature but key mismatch
    // - Invalid: Bad/missing signature or key
    return isKeyMatch ? TallyValidityStatus.VALID : TallyValidityStatus.WARNING;
  } catch (error) {
    console.error('Error getting tally validity status:', error);
    return TallyValidityStatus.INVALID;
  }
};

/**
 * Enhance tally objects with validity information
 * @param {Array} tallies - Array of tally objects
 * @returns {Promise<Array>} - Array of enhanced tally objects with validity info
 */
export const enhanceTalliesWithValidity = async (tallies) => {
  if (!tallies || !Array.isArray(tallies)) {
    return [];
  }
  
  const enhancedTallies = [];
  
  for (const tally of tallies) {
    const validityStatus = await getTallyValidityStatus(tally);
    enhancedTallies.push({
      ...tally,
      validity: {
        status: validityStatus
      }
    });
  }
  
  return enhancedTallies;
};