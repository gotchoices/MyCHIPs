# MyCHIPs Language Translation System

This folder contains translations for the MyCHIPs schema system in various languages.

## Current Languages

- Spanish (spa): Complete translation across all schemas
  - `mychips-spa.wmt` - Core MyCHIPs schema components
  - `json-spa.wmt` - JSON schema definitions
  - `wylib-spa.wmt` - In wyselib/schema/language/ - Wylib schema components
  - `base-spa.wmt` - In wyselib/schema/language/ - Base schema components
  - `wm-spa.wmt` - In wyselib/schema/language/ - Wyseman schema components
- Finnish (fin): Partial translations
  - `mychips-fin.wmt` - Partial MyCHIPs schema
  - `wylib-fin.wmt` - In wyselib/schema/language/ - Partial Wylib schema
- Nepali (nep): Partial translations
  - `mychips-nep.wmt` - Partial MyCHIPs schema
  - `json-nep.wmt` - Partial JSON schema
  - `base-nep.wmt` - In wyselib/schema/language/ - Partial Base schema
  - `wm-nep.wmt` - In wyselib/schema/language/ - Partial Wyseman schema
  - `wylib-nep.wmt` - In wyselib/schema/language/ - Partial Wylib schema

Each language has its own progress tracking file (`STATUS-{lang}.md`) that lists completed and pending translations.

## Schema Organization

MyCHIPs depends on several schema components that need translation:

1. **MyCHIPs Schema** (in current directory)
   - Primary application schema (tallies, chits, users, etc.)
   - Files: `mychips-{lang}.wmt`
   - Contains core business domain objects like tally, chit, lift

2. **JSON Schema** (in current directory)
   - JSON-specific data structures used for API/imports/exports
   - Files: `json-{lang}.wmt`
   - Used for data exchange formats and API inputs/outputs

3. **Wylib Schema** (in mychips/../wyselib/schema/language/)
   - UI components and application framework
   - Files: `wylib-{lang}.wmt`
   - Contains GUI elements, widgets, and application preferences

4. **Base Schema** (in mychips/../wyselib/schema/language/)
   - Fundamental data types and common structures
   - Files: `base-{lang}.wmt`
   - Original definitions found in mychips/../wyselib/schema/base/*.wmt (not .wms)
   - Includes key tables:
     - base.addr - Address information
     - base.comm - Communication methods
     - base.ent - Entity definitions
     - base.file - File storage
     - base.language - Language handling
     - base.parm - Parameter settings
     - base.priv - Privilege management
     - base.country - Country codes

5. **Wyseman Schema** (in mychips/../wyselib/schema/language/)
   - Schema management system itself
   - Files: `wm-{lang}.wmt`
   - Original definitions found in mychips/../wyseman/lib/run_time.wmt
   - Contains metadata tables, object tracking, and system messages

The file paths must be carefully managed:
- mychips-*.wmt and json-*.wmt files belong in mychips/schema/language/
- wylib-*.wmt, base-*.wmt, and wm-*.wmt files belong in mychips/../wyselib/schema/language/

When beginning a new language translation, all these components should be considered for complete system translation. The Spanish translation now has complete coverage across all schema components.

## Translation Workflows

### AI-Assisted Translation Process

When using AI tools to assist with translations:

1. Each language has a corresponding `STATUS-{lang}.md` file (e.g., `STATUS-spa.md` for Spanish) that tracks:
   - Last synchronization date with English files
   - Completed tables/views
   - Tables/views in progress
   - Pending tables/views
   - Translation decisions and terminology

2. The AI can directly:
   - Compare English and target language WMT files
   - Identify missing translations
   - Create translation patches containing just the missing elements
   - Update the STATUS file to track progress

3. When English schema files change:
   - Run `git log --since="[last synchronization date]" -- ../*.wmt` to find changes
   - Update the language-specific STATUS file with new work items
   - Track the current date as the new synchronization date

This direct comparison approach is much more efficient than the CSV workflow when using AI assistance, as it eliminates several intermediate steps.

#### Translation Process Steps

For each object or group of related objects:
1. Compare English WMT file with target language translation
2. Identify missing fields, messages, and descriptions
3. Create translations for missing elements
4. Update status in the STATUS file
5. Prepare patch file for missing translations

#### Translation Process Recommendations

1. **Group Related Objects**: Translate conceptually related objects together (all routes-related views, all chits tables/views, etc.) to maintain terminology consistency and context.

2. **Prioritize Active Components**: Skip translating deprecated views/tables (often marked with "Deprecated" in descriptions) to focus effort on active components.

3. **Base Tables First**: Translate base tables before their views to establish terminology that will be used throughout derived views.

4. **Update STATUS Files Immediately**: Record each translation in the STATUS file immediately after completion to maintain accurate progress tracking.

#### Prioritization Plan

For new languages, follow this order of translation:
1. Complete MyCHIPs core tables (tallies, chits, lifts)
2. Focus on UI-visible elements (chark, users_v_me)
3. Complete JSON schema for API functionality
4. Fill in remaining Wylib components
5. Add Base and Wyseman schema translations

### Terminology Management

#### Terminology Glossary

Maintaining consistent terminology across all database objects is crucial. Each language should maintain a comprehensive terminology glossary in its STATUS file, with format:

```
- "english term" -> "target_language_term" (back-translation: "english explanation")
```

The glossary should be updated whenever new key terms are translated, providing a single source of truth for all translations.

#### Component-Specific Terminology

Different schema components have specialized terminology:

1. **MyCHIPs Schema** - Key domain terms like:
   - tally, chit, lift, foil, stock, clutch
   - route, path, edge, node, circuit
   - digest, hash, chain

2. **Base Schema** - Common entity terms like:
   - entity, address, communication
   - country, language, parameter
   - file, media format, checksum

3. **Wyseman Schema** - Database metadata:
   - object, table, column, text
   - release, version, parameter
   - message, error code

For maximum consistency, translate the core MyCHIPs schema first to establish domain terminology, then expand to other components.

#### Technical Terms Strategy

For technical terms, follow these guidelines:
- Keep technical computing terms unchanged (JSON, UUID, hash, Base58, socket, etc.)
- Translate conceptual technical terms using domain-appropriate terminology
- Always document decisions in the glossary with back-translations

#### Field Translation Patterns

Maintain consistency in these common field patterns:
- Database timestamp fields: `crt_date` → "Creado", `mod_date` → "Modificado", etc.
- Standard boolean fields: `clean` → "Limpio", `valid` → "Válido", etc.
- ID fields: `*_ent` → "Entidad", `*_seq` → "Secuencia", etc.
- Digest/hash fields: Use "Resumen" for "digest" and maintain "hash" untranslated
- Min/max fields: "Mínimo" and "Máximo" with consistent prepositions

#### Terminology Consultation for Non-Speakers

When translating into languages you don't speak, the STATUS files include special **Terminology Consultation** sections designed to help with decision-making:

1. **Back-Translation Format:**
   ```
   "english term" translation options:
   - "target_language_term" [chosen] - Back-translation: "english explanation" - Context note
   - "alternative_term" - Back-translation: "alternative explanation" - Why this might be suitable
   ```

2. **Specific Questions:**
   Each consultation includes direct questions about the intended meaning of key terms that might have multiple possible translations.

3. **Context Notes:**
   Explanations about domain-specific usage (financial, technical, etc.) to help determine the most appropriate translation.

This approach allows non-speakers of the target language to make informed decisions about translations by understanding what the translated terms literally mean in English.

### Traditional Human Translation Process (Legacy Method)

The following method was designed for human translators who may prefer working with spreadsheets:

1. Determine the 3-letter ISO code (xyz, for example) for the new language
2. Edit test/mocha/language.js to include the code in the languages array (line 14)
3. Make sure the last two tests are actually enabled in language.js (line 103)
4. Do: cd test/auto/schema; npx mocha dbinit language (the final test should show failures)
5. This should create CSV files in the data dir for any tags missing in the target language
6. Open the newly created CSV file in a spreadsheet
7. Perform the translation, filling in title and help columns for all applicable tags
8. Make sure the file is saved back in CSV format
9. Be in the mychips/schema folder (the following utilities consult Wyseman.conf)
10. Import new language tags into the db:
    ```
    wm-csv2db <the_file_name>.csv
    ```
11. Check in wm.table_lang (and/or UI applications) for the correct language data
12. Create wyseman language files:
    ```
    wm-db2wmt -s mychips -l <xyz> >language/<schema>-<xyz>.wmt
    ```
13. There are several schemas to consider (wm, wylib, base, mychips, json)
14. Try to rebuild from source: "make clean lang" and make sure all tags still present in DB
15. Rebuild schema files: "make schema sql" and then rerun language test above
16. Create a `STATUS-xyz.md` file to track translation progress
17. When satisfied, submit P/R to mychips/wyselib with language translation files/updates

### Final Integration (Both Methods)

Regardless of which method is used, the final steps are:

1. Verify translations with native speakers if possible
2. Update the schema files with `make clean lang`
3. Verify everything builds correctly with `make schema sql`
4. For components outside the mychips directory (such as wylib in wyselib):
   - Navigate to the respective directory (e.g., `cd ../wyselib/schema`)
   - Run `make clean lang` and `make schema sql` there as well
   - Ensure all components build correctly and language tags are properly integrated
5. Test the application with the new language settings to verify actual display 
6. Submit changes via pull request for each affected repository (mychips, wyselib, etc.)

### Important Notes

#### File Location
- MyCHIPs schema translations (mychips-*.wmt, json-*.wmt) belong in mychips/schema/language/
- Base, Wylib, and Wyseman translations (base-*.wmt, wylib-*.wmt, wm-*.wmt) belong in mychips/../wyselib/schema/language/
- The STATUS-*.md tracking files should remain in mychips/schema/language/ for all components

#### Finding Schema Definitions
- **MyCHIPs Core Files**: Located in mychips/schema/*.wmt
- **Base Schema Files**: Located in mychips/../wyselib/schema/base/*.wmt (not .wms as previously documented)
- **Wyseman Runtime**: Located in mychips/../wyseman/lib/run_time.wmt
- **Wylib Files**: Located in mychips/../wyselib/schema/wylib.wmt

When translating for a new language, you should:
1. First find the original source .wmt file containing English definitions
2. Examine each table, field, error message, and value that needs translation
3. Create a properly structured .wmt file for the target language

#### WMT File Format and Structure
- Use `tabtext table_name -lang xyz` format for table definitions
- For each table, include the table title and description
- For each field, include a field name, title, and description
- For enum values, include each value, title and description
- For error messages, use the -errors flag
- Use proper spacing and indentation to maintain readability

#### Session Restoration Guide

When returning to translation work after a session break or context compaction:

1. **Review Status Files First**:
   - Check STATUS-*.md files to understand what's completed and what remains
   - Note any terminology decisions already made in the "Translation Decisions" section
   - Identify priority tasks marked for completion

2. **Examine Existing Translations**:
   - Look at completed translations in both the current language and Spanish for reference
   - Check for consistent terminology patterns across related tables
   - Note any specific formatting or style choices

3. **Compare With English Sources**:
   - Always refer to the original English definitions when creating new translations
   - Use the file paths in "Finding Schema Definitions" to locate source files
   - Ensure you're translating from the most current English schema

4. **Maintain Consistency**:
   - Re-read the "Terminology Glossary" in the language's STATUS file
   - Use the same translation for recurring terms (particularly domain-specific terms)
   - Match formatting styles from previous work

5. **Testing Workflow**:
   - After creating translations, verify they match the expected format
   - Follow the integration steps in the "Final Integration" section
   - Record all completed work in the STATUS file immediately

#### Schema Dependencies
If the language description for a table/view does not exist, there is nothing to
relate column/message/value tags to so even though they may import (wm-csv2db), they will 
not export (wm-db2wmt) and so will be lost.

The following query can show how many tags you have installed for a given language:
```sql
select sorter,title from wm.language 
  where fr_lang = 'eng' and language = 'nep' and title notnull
```

Make sure to have the development schema installed "make dev" to access that view.

The "-s schema" switch to wm-db2wmt will limit the output to those tables/views belonging
to the specified schema. If you are translating tables/views that are part of wyselib,
make sure to include those in the wyselib/schema/language folder rather than as part of
the mychips repo.