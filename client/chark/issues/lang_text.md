# Language Text Tags Implementation

**Status: IN PROGRESS** - Key Management screens fixed as proof of concept

## Background & Technical Details

### Language Text System
- Language text in MyCHIPs mobile app is fetched from the backend database through Wyseman
- Each language tag typically contains two properties:
  - `title` - Short text for buttons, labels, headers
  - `help` - Longer descriptive text for context help popups

### Database Structure
Tags are stored in several database tables, organized by type:

1. **Table Tags**: General descriptions of database tables
   - Table: `wm.table_text`
   - Fields: `tt_sch, tt_tab, language, title, help`

2. **Column Tags**: Descriptions of specific table columns 
   - Table: `wm.column_text`
   - Fields: `ct_sch, ct_tab, ct_col, language, title, help`

3. **Value Tags**: Descriptions of specific values a column can assume
   - Table: `wm.value_text`
   - Fields: `vt_sch, vt_tab, vt_col, value, language, title, help`

4. **Message Tags**: Arbitrary codes associated with tables/views
   - Table: `wm.message_text`
   - Fields: `mt_sch, mt_tab, code, language, title, help`

### Namespace Organization
- Tags are assigned in the DB by 'view' (or table)
- The tag namespace is specific to each view/table
- Special case: `chark` is a pseudo-view for mobile app-specific tags that don't relate to a specific DB table

### Querying Language Tags
A user with SSH permissions can query language tags using:

```shell
ssh admin@mychips.net "psql mychips admin -c \"select * from <some_table> where ...\""
```

Example queries:
```sql
-- Query all message tags for the chark app in English
select mt_sch, mt_tab, code, language, title 
from wm.message_text 
where language = 'eng' and mt_tab = 'chark';

-- Query column tags for tallies view
select ct_sch, ct_tab, ct_col, language, title 
from wm.column_text 
where language = 'eng' and ct_tab = 'mychips.tallies_v_me';
```

## Current Issues

1. **Inconsistent Implementation**:
   - Text tags are accessed inconsistently across components
   - Some components use HelpText with both title and help, others use raw Text elements
   - Components handle missing translations differently (some show nothing, others use hardcoded text)

2. **Missing Translations**:
   - Not all language tags are populated in the backend database
   - Some buttons appear with no text in the UI (e.g., in KeyManagement screens)
   - Developers have no clear indication when translations are missing

3. **Code Organization**:
   - Multiple patterns for fetching and displaying text
   - Hook dependencies are inconsistently managed
   - No standardized fallback pattern for missing translations

## Goals

1. **Standardize Implementation**:
   - Implement a common method for accessing language text across all components
   - Display raw tags (e.g., 'chark:tag:property') when translations are missing
   - Add consistent HelpText components with help icons where contextual help is available

2. **Identify Missing Tags**:
   - Query the database to identify existing tags
   - Compare with tags used in the codebase
   - Generate SQL for adding missing tags

3. **Developer Experience**:
   - Make missing translations immediately obvious through visual indicators
   - Create tools to help identify and fix missing translations

## Tactical Approach

### Phase 1: Standardize Text Display (Current Phase)
1. Update components to use a consistent pattern for displaying text
2. Implement fallback to display tag names when translations are missing
3. Focus first on KeyManagement screens, which have known missing translations

### Phase 2: Database Tag Verification
1. Query the database for existing tags using the provided SQL examples
2. For each component using language tags:
   - Identify which tags should exist in the database
   - Check if they actually exist and have both title and help properties
   - Generate SQL for adding missing tags

### Phase 3: Broader Implementation
1. Gradually update all components to use the standardized approach
2. Add better error handling and logging for translation loading
3. Consider creating a developer tool to report missing translations

## Key Findings and Reference Info

### Existing Key Management Tags
The database already contains all the necessary tags for the key management screens:

```sql
-- Key management related tags
SELECT mt_sch, mt_tab, code, language, title 
FROM wm.message_text 
WHERE language = 'eng' 
  AND mt_tab = 'chark' 
  AND code IN ('keygen', 'import', 'export', 'keywarn', 'keypass', 'keys', 'private', 'public', 'nokey', 'biofail', 'keybio', 'success');
```

| Code    | Title                | Purpose                                |
|---------|----------------------|----------------------------------------|
| keygen  | Generate Key         | Key generation button/header           |
| import  | Import               | Import key button/header               |
| export  | Export               | Export key button/header               |
| keywarn | Overwrite Key?       | Warning when replacing existing key    |
| keypass | Key Pass Phrase      | Passphrase input for key protection    |
| keys    | Manage Keys          | Main key management screen title       |
| private | Private Key          | Private key section header             |
| public  | Public Key           | Public key section header              |
| nokey   | No Signing Key       | Notice when no key exists              |
| biofail | Biometric Failure    | Error when biometric auth fails        |
| keybio  | Biometric Validation | Biometric validation explanation       |
| success | Success              | Generic success message                |

## Progress Tracking

### ✅ Completed
- Updated KeyManagement screens to use proper language tags:
  - Fixed GenerateKey component to use `keygen` tag instead of hardcoded text
  - Standardized fallback pattern to show tag name when translation is missing
  - Verified database already contains needed tags (keygen, import, export, etc.)
- Confirmed query method works for checking existing database tags

### 🔲 Next Steps (Priority Order)
1. Create utility function in `src/utils/language.js`:
   ```javascript
   // Add standardized language access function
   export function getLanguageText(textObj, tag, property = 'title', view = 'chark') {
     const text = textObj?.[tag]?.[property];
     if (text) return text;
     return `${view}:${tag}:${property}`;
   }
   ```

2. Review and fix screens with known missing translations:
   - [ ] Review all screens in Settings section
   - [ ] Review Tally screens and their components
   - [ ] Review Profile screens

3. Perform wider component audit:
   - [ ] Create list of all components using language text
   - [ ] Check which ones handle missing translations properly
   - [ ] Update remaining components to use standardized approach

### 🔲 Future Enhancements
1. Create developer tools to identify missing translations:
   - [ ] Script to scan codebase for language tag usage
   - [ ] Compare with database tags to find missing entries
   - [ ] Generate SQL for adding missing tags

2. Consider Redux optimization:
   - [ ] Evaluate if language text should be stored in Redux for persistence
   - [ ] Create appropriate slices and reducers if needed

## Recommended Query for Checking Tags
When working on a specific screen or component, use this query to check for existing tags:

```sql
-- Replace 'component_name' with relevant tags
SELECT mt_sch, mt_tab, code, language, title, help 
FROM wm.message_text 
WHERE language = 'eng' 
  AND mt_tab = 'chark' 
  AND code IN ('tag1', 'tag2', 'tag3')
ORDER BY code;
```

## Success Criteria
- Components consistently display text using the standardized approach
- Missing translations show clear tag identifiers (e.g., "chark:keygen:title")
- Database has complete set of required language tags
- Help text is available where appropriate