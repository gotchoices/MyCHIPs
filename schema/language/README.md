# MyCHIPs Language Translation System

This folder contains translations for the MyCHIPs schema system in various languages.

## Current Languages

- Spanish (spa): `mychips-spa.wmt` - Most comprehensive, includes core system components
- Finnish (fin): `mychips-fin.wmt` - Partial translation
- Nepali (nep): `mychips-nep.wmt` - Partial translation

Each language has its own progress tracking file (`STATUS-{lang}.md`) that lists completed and pending translations.

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

#### Translation Process Recommendations

1. **Group Related Objects**: Translate conceptually related objects together (all routes-related views, all chits tables/views, etc.) to maintain terminology consistency and context.

2. **Prioritize Active Components**: Skip translating deprecated views/tables (often marked with "Deprecated" in descriptions) to focus effort on active components.

3. **Base Tables First**: Translate base tables before their views to establish terminology that will be used throughout derived views.

4. **Update STATUS Files Immediately**: Record each translation in the STATUS file immediately after completion to maintain accurate progress tracking.

### Terminology Management

#### Terminology Glossary

Maintaining consistent terminology across all database objects is crucial. Each language should maintain a comprehensive terminology glossary in its STATUS file, with format:

```
- "english term" -> "target_language_term" (back-translation: "english explanation")
```

The glossary should be updated whenever new key terms are translated, providing a single source of truth for all translations.

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
4. Submit changes via pull request

### Important Notes

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