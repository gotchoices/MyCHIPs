# Language Handling Strategy for MyCHIPs Mobile App

*Created: April 5, 2025*  
*Updated: April 5, 2025*

## Overview

This document outlines the strategy for handling multiple languages in the MyCHIPs mobile app, including language detection, default behavior, user preferences, and implementation details.

## Current Status ✅

We've resolved the language handling issues in the app:

1. ✅ Fixed: On first launch, the language dropdown in Settings now properly shows "English" instead of empty parentheses "()"
2. ✅ Implemented: The app now detects and uses the device's locale when determining initial language
3. ✅ Improved: The connection between frontend language codes and backend language data is now optimized
4. ✅ Maintained: The app continues to use 3-letter codes (ISO 639-2) internally for backend compatibility while also storing 2-letter codes for device locale matching

## Language Code Strategy

The backend provides both ISO 639-1 (2-letter) and ISO 639-2 (3-letter) language codes via the `base.language_v` view. Our strategy is to:

1. Continue using 3-letter codes (ISO 639-2) for backend communication to maintain compatibility
2. Additionally store and use 2-letter codes (ISO 639-1) for device locale matching
3. Query both from the backend rather than maintaining a separate mapping table

## Implemented Language Detection Flow

The language detection flow now follows this sequence:

1. English is set as the default in Redux initial state (ensuring UI always shows a value)
2. The app establishes connection to the backend
3. After connection is established, we:
   - Check if user has explicitly selected a language previously (AsyncStorage)
   - If yes, we use that language
   - If no:
     a. Query available languages from backend
     b. Get device locale
     c. If device locale language is supported, switch to it
     d. If not supported, stay with English default

## Implementation Details

### 1. Updated Redux Initial State

English is now explicitly set as the default:

```javascript
// In profileSlice.js
const initialState = {
  // ...other properties
  preferredLanguage: {
    name: 'English',
    code: 'eng',
    iso_2: 'en'
  }
};
```

### 2. Language Detection Thunk

We created a new thunk that runs after backend connection is established, but only for first-time users:

```javascript
export const detectAndSetLanguage = createAsyncThunk(
  'profile/detectAndSetLanguage',
  async (wm, { dispatch, getState }) => {
    try {
      // Check if user has explicitly selected a language previously
      const storedPreference = await AsyncStorage.getItem('preferredLanguage');
      if (storedPreference) {
        // User already has a preference, no need to detect
        return null;
      }
      
      // Get device locale
      const deviceLocale = getDeviceLocale();
      
      // Get available languages
      const availableLanguages = await getAvailableLanguages(wm);
      
      // Find matching language
      const matchedLanguage = findMatchingLanguage(deviceLocale, availableLanguages);
      
      if (matchedLanguage) {
        // Found a match to device locale, update language
        wm.newLanguage(matchedLanguage.code);
        
        // Save preference
        await AsyncStorage.setItem('preferredLanguage', JSON.stringify(matchedLanguage));
        
        return {
          name: matchedLanguage.eng_name,
          code: matchedLanguage.code,
          iso_2: matchedLanguage.iso_2
        };
      }
      
      // No match found, keep English default
      return null;
    } catch (error) {
      console.log('Error detecting language:', error);
      return null;
    }
  }
);
```

### 3. Updated Language Components

1. Modified the query in `Language/index.jsx` to include both code formats:

```javascript
wm.request(`language_ref_${random()}`, 'select', {
  view: 'base.language_v',
  fields: ['code', 'iso_2', 'eng_name', 'tables'],
  where: {
    oper: 'notnull',
    left: 'tables',
  },
}, data => {
  setLanguages(data ?? [])
})
```

2. Updated the language save function to store both code formats:

```javascript
dispatch(setPreferredLanguage({
  name: found?.eng_name,
  code: found?.code,
  iso_2: found?.iso_2
}));
AsyncStorage.setItem('preferredLanguage', JSON.stringify(found));
```

### 4. Connection Integration

Added language detection to the socket connection flow, but only for first-time users:

```javascript
websocket.onopen = async () => {
  // ... existing connection code ...
  
  // Check if we should perform language detection
  try {
    const storedPreference = await AsyncStorage.getItem('preferredLanguage');
    if (!storedPreference) {
      // Only detect language if there's no stored preference (first time use)
      dispatch(detectAndSetLanguage(wm));
    }
  } catch (error) {
    console.log('Error checking language preference:', error);
  }
  
  // ... existing socket listener code ...
};
```

### 5. Language Utilities

Created new utility functions in `language.js`:

```javascript
// Get device locale in normalized format
export function getDeviceLocale() {
  try {
    let locale;
    if (Platform.OS === 'ios') {
      locale = NativeModules.SettingsManager.settings.AppleLocale || 
               NativeModules.SettingsManager.settings.AppleLanguages[0];
    } else {
      locale = NativeModules.I18nManager.localeIdentifier;
    }

    return locale.split(/[-_]/)[0].toLowerCase();
  } catch (error) {
    console.log('Error getting device locale:', error);
    return 'en'; // Default to English
  }
}

// Query available languages with caching
export async function getAvailableLanguages(wm) {
  try {
    // Try cache first
    const cachedData = await AsyncStorage.getItem('availableLanguages');
    if (cachedData) {
      const { timestamp, languages } = JSON.parse(cachedData);
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
```

## Benefits Realized

This implementation provides several benefits:

1. **Better User Experience**:
   - App now respects device language settings for first-time users
   - Clear visual feedback in language dropdown (no more empty parentheses)
   - Consistent language experience across sessions

2. **Technical Advantages**:
   - Maintains compatibility with backend 3-letter codes
   - Leverages existing backend data structures
   - Clean separation of concerns

3. **Performance Considerations**:
   - Only performs locale detection when needed (no stored preference)
   - Caches language data to reduce unnecessary backend queries
   - Minimal overhead in the connection process

## Verification

The implementation has been tested and verified:

1. ✅ First launch behavior:
   - App properly shows English by default in the dropdown
   - If device locale matches a supported language, it switches to that language

2. ✅ User preference persistence:
   - When a language is manually selected, it persists across app restarts
   - User preference takes precedence over device locale

3. ✅ UI components:
   - Dropdown correctly shows the currently selected language
   - No empty parentheses or missing text in the language selector

## Future Enhancements

Potential future improvements:

1. Add a setting to explicitly enable/disable automatic language detection based on device locale
2. Implement a more robust i18n library if language needs expand beyond current requirements
3. Add visual indicators when language is being switched
4. Add unit tests for language detection logic

## Technical Notes for Future Reference

### Backend Language Data

1. **Available Languages Query**: The backend exposes language information via the `base.language_v` view:
   ```sql
   SELECT code, iso_2, eng_name, tables FROM base.language_v WHERE tables NOTNULL;
   ```

2. **Current Language Support**: As of April 2025, the backend supports:
   - English (`eng`/`en`): 122 tables
   - Finnish (`fin`/`fi`): 3 tables
   - Nepali (`nep`/`ne`): 118 tables
   - Spanish (`spa`/`es`): 31 tables

3. **Language Table Structure**:
   - `code`: 3-letter ISO 639-2 code (primary key)
   - `iso_2`: 2-letter ISO 639-1 code (for device locale matching)
   - `eng_name`: English name of the language
   - `tables`: Count of tables with translations in this language

### Key Files and Components

1. **Redux State**: 
   - `src/redux/profileSlice.js` - Contains language state and thunks
   - Initial state sets English as default with both 2 and 3-letter codes

2. **UI Components**:
   - `src/screens/Setting/Language/index.jsx` - Language selection screen
   - Updated to query and store both 2 and 3-letter codes

3. **Utility Functions**:
   - `src/utils/language.js` - Contains language utility functions
   - Added device locale detection, language matching, and caching

4. **Connection Integration**:
   - `src/components/SocketProvider.jsx` - Triggers language detection on first connection
   - Only detects language when no user preference exists

### Common Issues and Solutions

1. **Empty Language Dropdown**: Fixed by explicitly setting English as default in Redux initial state.

2. **AsyncStorage Import**: Make sure SocketProvider imports AsyncStorage when checking preferences:
   ```javascript
   import AsyncStorage from '@react-native-async-storage/async-storage';
   ```

3. **Testing Device Locale**: A test override can be implemented in `getDeviceLocale()`:
   ```javascript
   // For testing
   return 'ne'; // Override with Nepali for testing
   ```
   
4. **Race Conditions**: Language detection happens after socket connection is established, so any UI components that need the language before that point should fall back gracefully to the default language.

### Wyseman Language Integration

The `wm.newLanguage(code)` method should only be called:
1. When explicitly changing language (user selection)
2. When restoring a stored preference
3. When automatically setting language based on device locale (first-time use)

Do not call it when defaulting to English, as this happens automatically when no language is specified.