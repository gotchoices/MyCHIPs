// Deep link utilities for MyCHIPs
// Copyright MyCHIPs.org

import { v4 as uuid } from 'uuid';
import qs from 'query-string';

/**
 * Link types used throughout the app
 */
export const LINK_TYPES = {
  TICKET: 'ticket',
  INVITE: 'invite',
  PAY: 'pay',
  SIGNKEY: 'signkey'
};

/**
 * Full URL prefixes for each link type
 */
export const LINK_PREFIXES = {
  TICKET: 'https://mychips.org/ticket',
  INVITE: 'https://mychips.org/invite',
  PAY: 'https://mychips.org/pay',
  SIGNKEY: 'https://mychips.org/signkey'
};

/**
 * Add a UUID to a URL to ensure uniqueness for navigation
 * This helps with repeated deep links being processed correctly
 * 
 * @param {string} url - The URL to add a UUID to
 * @returns {string} The URL with a UUID parameter added
 */
export function addUuidToUrl(url) {
  return `${url}${url.includes('?') ? '&' : '?'}randomString=${uuid()}`;
}

/**
 * Extract the path type from a URL
 * For example, 'https://mychips.org/signkey?s=123' returns 'signkey'
 * 
 * @param {string} url - The URL to extract the path type from
 * @returns {string} The path type (last segment of the URL path)
 */
export function extractPathType(url) {
  if (!url) return null;
  
  const pathWithoutParams = url?.split('?')?.[0] || '';
  const pathSegments = pathWithoutParams.split('/');
  return pathSegments[pathSegments.length - 1];
}

/**
 * Check if a URL is a specific type of deep link
 * 
 * @param {string} url - The URL to check
 * @param {string} linkType - The link type from LINK_TYPES
 * @returns {boolean} True if the URL is of the specified type
 */
export function isLinkType(url, linkType) {
  if (!url) return false;
  
  // First check direct prefix match
  if (url.startsWith(LINK_PREFIXES[linkType])) {
    return true;
  }
  
  // Then check path type
  const pathType = extractPathType(url);
  return pathType === LINK_TYPES[linkType];
}

/**
 * Parse a signkey URL into the JSON format expected by the app
 * 
 * @param {string} url - The signkey URL to parse
 * @returns {string|null} JSON string for the signkey or null if invalid
 */
export function parseSignkeyUrl(url) {
  try {
    // Parse the URL to extract parameters
    const parsed = qs.parseUrl(url);
    const params = parsed.query;
    
    // Validate required parameters
    if (!params.s || !params.i || !params.d) {
      console.error("Missing required parameters in signkey URL");
      return null;
    }
    
    // Create the signkey JSON format expected by decryptJSON
    return JSON.stringify({
      signkey: {
        s: params.s,
        i: params.i,
        d: params.d
      }
    });
  } catch (error) {
    console.error('Error processing URL:', error);
    return null;
  }
}