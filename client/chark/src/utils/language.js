/**
 * Language utility functions for MyCHIPs mobile app
 */
import { Platform, NativeModules } from 'react-native';
import AsyncStorage from '@react-native-async-storage/async-storage';
import { random } from './common';

// Cache key for stored available languages
const LANGUAGES_CACHE_KEY = 'availableLanguages';
// Cache expiration time (1 week in milliseconds)
const CACHE_TTL = 7 * 24 * 60 * 60 * 1000;

/**
 * Gets the device locale in a normalized format
 * @returns {string} The 2-letter ISO language code
 */
export function getDeviceLocale() {
  try {
    // FOR TESTING: Uncomment to override with Nepali for testing
    // return 'ne';

    let locale;
    if (Platform.OS === 'ios') {
      locale = NativeModules.SettingsManager.settings.AppleLocale || 
               NativeModules.SettingsManager.settings.AppleLanguages[0];
    } else {
      locale = NativeModules.I18nManager.localeIdentifier;
    }

    // Handle locales like en-US, extract just the language part
    return locale.split(/[-_]/)[0].toLowerCase();
  } catch (error) {
    console.log('Error getting device locale:', error);
    return 'en'; // Default to English
  }
}

/**
 * Queries available languages from the backend
 * @param {Object} wm - Wyseman client instance
 * @returns {Promise} Promise resolving to array of available languages
 */
export function queryAvailableLanguages(wm) {
  return new Promise((resolve) => {
    wm.request(`lang_query_${random()}`, 'select', {
      view: 'base.language_v',
      fields: ['code', 'iso_2', 'eng_name', 'tables'],
      where: {
        oper: 'notnull',
        left: 'tables',
      },
    }, data => {
      if (data && data.length > 0) {
        // Cache the results with timestamp
        const cacheData = {
          timestamp: Date.now(),
          languages: data
        };
        AsyncStorage.setItem(LANGUAGES_CACHE_KEY, JSON.stringify(cacheData));
      }
      resolve(data || []);
    });
  });
}

/**
 * Gets available languages from cache or queries backend
 * @param {Object} wm - Wyseman client instance
 * @returns {Promise} Promise resolving to array of available languages
 */
export async function getAvailableLanguages(wm) {
  try {
    // Try to get from cache first
    const cachedData = await AsyncStorage.getItem(LANGUAGES_CACHE_KEY);
    if (cachedData) {
      const { timestamp, languages } = JSON.parse(cachedData);
      // Check if cache is still valid
      if (Date.now() - timestamp < CACHE_TTL && languages?.length > 0) {
        return languages;
      }
    }
    
    // If cache invalid or missing, query backend
    return await queryAvailableLanguages(wm);
  } catch (error) {
    console.log('Error getting available languages:', error);
    return [];
  }
}

/**
 * Finds matching language based on device locale
 * @param {string} locale - Device locale code (2-letter)
 * @param {Array} availableLanguages - Array of available languages
 * @returns {Object|null} Matching language object or null if no match
 */
export function findMatchingLanguage(locale, availableLanguages) {
  if (!locale || !availableLanguages || availableLanguages.length === 0) {
    return null;
  }
  
  // Find language with matching iso_2 code
  return availableLanguages.find(lang => 
    lang.iso_2 && lang.iso_2.toLowerCase() === locale.toLowerCase()
  );
}

/**
 * Gets language text with fallback to a standardized format when translation is missing
 * @param {Object} textObj - The object containing language texts (typically from useMessageText)
 * @param {string} tag - The language tag to retrieve (e.g., 'keygen', 'import')
 * @param {string} property - The property to retrieve ('title' or 'help'), defaults to 'title'
 * @param {string} view - The database view/namespace for the tag, defaults to 'chark'
 * @return {string} - The translated text or a standardized fallback format
 */
export function getLanguageText(textObj, tag, property = 'title', view = 'chark') {
  // Add better handling for undefined/null textObj
  if (!textObj) return `${view}:${tag}:${property}`;
  
  // Safely access the text
  const text = textObj[tag]?.[property];
  
  // Return text if it exists and is a string, otherwise return the formatted tag
  if (text && typeof text === 'string') return text;
  return `${view}:${tag}:${property}`;
}