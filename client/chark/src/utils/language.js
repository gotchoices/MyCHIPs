/**
 * Gets language text with fallback to a standardized format when translation is missing
 * @param {Object} textObj - The object containing language texts (typically from useMessageText or similar hooks)
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

