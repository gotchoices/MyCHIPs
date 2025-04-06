# Spanish (spa) Translation Status

Last synchronized with English: April 5, 2025

## Completed Tables/Views
- [x] mychips.tallies (completely translated with improved terminology)
- [x] mychips.users (completely translated)
- [x] mychips.users_v (completely translated)
- [x] mychips.chits (completely translated)
- [x] mychips.chits_v (completely translated)
- [x] mychips.chits_v_me (completely translated)
- [x] mychips.chits_v_chains (completely translated)
- [x] mychips.chit_tries (completely translated)
- [x] mychips.lifts (completely translated)
- [x] mychips.lifts_v (completely translated)
- [x] mychips.lifts_v_me (completely translated)
- [x] mychips.lifts_v_dist (completely translated)
- [x] mychips.lifts_v_pay (completely translated)
- [x] mychips.lifts_v_pay_me (completely translated)
- [x] mychips.tallies_v (completely translated)
- [x] mychips.tallies_v_me (completely translated)
- [x] mychips.tallies_v_edg (completely translated)
- [x] mychips.tallies_v_net (completely translated)
- [x] mychips.tallies_v_paths (completely translated)
- [x] mychips.routes (completely translated)
- [x] mychips.routes_v (completely translated)
- [x] mychips.route_tries (completely translated)
- [x] mychips.routes_v_paths (completely translated)
- [x] mychips.routes_v_query (completely translated)
- [x] mychips.agents (completely translated)
- [x] mychips.agents_v (completely translated)
- [x] mychips.contracts (completely translated)
- [x] mychips.contracts_v (completely translated)
- [x] mychips.creds (completely translated)
- [x] mychips.creds_v (completely translated)
- [x] mychips.file_v_me (completely translated)
- [x] mychips.file_v_part (completely translated)

## In Progress
None currently - completed the initially identified issues.

## Terminology Consultation

For non-Spanish speakers reviewing this translation, here are the key terminology choices with back-translations and context:

### "chit" translation options:
- **"vale"** [chosen] - Back-translation: "voucher" or "receipt" - A document representing value or credit
- **"nota"** - Back-translation: "note" - A record of something owed

Update: Understanding that a "chit" is like a notch in a historical tally stick representing something owed that can be called in, "vale" is still the preferred translation as it better conveys a formal record of value that can be redeemed.

### "foil" translation options:
- **"contraparte"** [chosen] - Back-translation: "counterpart" - The opposing part in a relationship
- **"frustrar"** [original translation] - Back-translation: "to frustrate" - This seems incorrect in context

Confirmed: "contraparte" is appropriate for "foil" as it correctly conveys the counterpart relationship in the tally.

### "clutch" translation options:
- **"retención"** [revised choice] - Back-translation: "retention" - The action of keeping or maintaining
- **"agarre"** [previous choice] - Back-translation: "grip" - More of a verb form or action of gripping
- **"embrague"** [original translation] - Back-translation: "mechanical clutch" - A mechanical device

Update: Based on feedback that "agarre" is more verb-like, "retención" is now the preferred translation as it better conveys the noun form of something that is held or retained.

### "lift" translation options:
- **"elevación"** [chosen] - Back-translation: "elevation" or "raising" - The act of moving something upward
- **"levantamiento"** - Back-translation: "lifting" - Similar meaning but longer word
- **"alza"** - Back-translation: "rise" - Could work but less precise

The term "elevación" was chosen for "lift" as it clearly conveys the concept of raising or elevating value through the network.

## Pending Translation Audit

### json Schema Objects
- [ ] json.cert
- [ ] json.connect
- [ ] json.contract
- [ ] json.file
- [ ] json.place
- [ ] json.tally
- [ ] json.user
- [ ] json.users

### mychips Schema Objects
- [x] mychips.addr_v_me (completed April 6, 2025)
- [x] mychips.chark (completed April 6, 2025)
- [ ] mychips.tallies_v_sum (deprecated - no translation needed)
- [x] mychips.tally_tries (completed April 6, 2025)
- [x] mychips.tokens (completed April 6, 2025)
- [x] mychips.tokens_v (completed April 6, 2025)
- [x] mychips.tokens_v_me (completed April 6, 2025)
- [x] mychips.users_v_flat (completed April 6, 2025)
- [x] mychips.users_v_me (completed April 6, 2025)
- [x] mychips.users_v_tallies (completed April 6, 2025)
- [x] mychips.users_v_tallies_me (completed April 6, 2025)
- [x] mychips.users_v_tallysum (completed April 6, 2025)

### Other Schema Objects
- [ ] wylib.data

## Translation Process for Each Object

For each object:
1. Compare English WMT file with Spanish translation
2. Identify missing fields, messages, and descriptions
3. Create translations for missing elements
4. Update status in this TODO file
5. Prepare patch file for missing translations

## Translation Decisions and Terminology

The following terminology decisions have been implemented:
- "tally" -> "recuento" (back-translation: "count" or "tally")
- "foil" -> "contraparte" (back-translation: "counterpart") [improved from "frustrar"]
- "stock" -> "existencias" (back-translation: "stock" or "inventory")
- "CHIP" remains "CHIP" (not translated)
- "lift" -> "elevación" (back-translation: "elevation" or "raising")
- "digest" -> "resumen criptográfico" (back-translation: "cryptographic summary") [improved from "resumen de hachís"]
- "clutch" -> "retención" (back-translation: "retention") [revised from "agarre" and improved from "embrague"]
- "chit" -> "vale" (back-translation: "voucher" or "receipt")
- "asset" -> "activo" (back-translation: "asset" - standard financial term)
- "liability" -> "pasivo" (back-translation: "liability" - standard financial term)
- "route" -> "ruta" (back-translation: "route" or "path")
- "pathway" -> "vía" (back-translation: "way" or "path")
- "edge" -> "enlace" (back-translation: "link")
- "node" -> "nodo" (back-translation: "node")
- "tries" -> "intentos" (back-translation: "attempts" or "tries")
- "lading" -> "cargamento" (back-translation: "cargo" or "shipment")
- "contract" -> "contrato" (back-translation: "contract")
- "section" -> "sección" (back-translation: "section")
- "publish" -> "publicar" (back-translation: "publish")
- "credentials" -> "credenciales" (back-translation: "credentials")
- "score" -> "puntuación" (back-translation: "score" or "points")
- "present" -> "presente" (back-translation: "present")
- "absent" -> "ausente" (back-translation: "absent")
- "file" -> "archivo" (back-translation: "file")
- "media" -> "medio" (back-translation: "medium")
- "format" -> "formato" (back-translation: "format")
- "comment" -> "comentario" (back-translation: "comment")
- "token" -> "token" (no translation - technical term kept as-is)
- "hash" -> "hash" (no translation - technical term kept as-is)
- "agent" -> "agente" (back-translation: "agent")
- "peer" -> "par" or "igual" (back-translation: "peer" or "equal")

## Completed Translations

### April 6, 2025 (Second Session)
- Completed user profile views and related objects
  - mychips.addr_v_me
  - mychips.users_v_flat 
  - mychips.users_v_me
  - mychips.users_v_tallies
  - mychips.users_v_tallies_me
  - mychips.users_v_tallysum
  - Translated all user certificate fields
  - Used consistent translations for identity information
  - Translated certificate related fields using same terminology as tally certificates
  - Aligned terminology with other personal data translations
  - Used "Dirección" for "Address" consistently across physical and CHIP contexts
  - Translated birth record data fields using "Nacimiento" terminology

- Completed mobile app related translations
  - mychips.chark
  - Translated all UI text elements for mobile application
  - Used consistent button and action terminology
  - Added appropriate translations for certificate, key management, and security concepts
  - Used "Clave" for cryptographic key concepts
  - Translated all key management and certificate related warning messages

- Completed tokens related tables/views
  - mychips.tokens
  - mychips.tokens_v
  - mychips.tokens_v_me
  - Translated all fields and descriptions
  - Maintained "token" as untranslated technical term
  - Translated "reuse" as "reutilizable"
  - Used consistent terminology for token expiration concepts
  - Used consistent field translations matching other objects (created, modified, etc.)

- Completed infrastructure tables
  - mychips.tally_tries
  - Translated all fields and descriptions
  - Used "Intentos" for "Tries" consistently
  - Maintained established terminology including "recuento" for "tally"
  - Used same terminology patterns for timestamp fields as in other tables

### April 6, 2025 (First Session)
- Completed tally network views
  - mychips.tallies_v_edg
  - mychips.tallies_v_net
  - mychips.tallies_v_paths
  - Translated all fields with consistent terminology
  - Used "enlace" for "edge" and "vía" for "path" 
  - Maintained consistent terminology for lift-related concepts
  - Translated network graph terminology (nodos, enlaces, circuito)
  - Distinguished between terms like "Nodo de Entrada" and "Entrada Extranjera"

- Completed additional route-related views
  - mychips.routes_v_paths
  - mychips.routes_v_query
  - Translated all fields in both views
  - Used "ruta" for "route" and "vía" for "pathway" consistently
  - Distinguished between internal "vía" (path) and external "ruta" (route) in field names
  - Maintained consistent terminology with previously translated route objects

- Completed file-related views
  - mychips.file_v_me
  - mychips.file_v_part
  - Translated all fields in both views
  - Used "archivo" for "file" consistently
  - Used "resumen" for "digest"
  - Kept technical term "hash" unchanged
  - Translated "media" as "medio" and "format" as "formato"

- Completed credentials-related tables/views
  - mychips.creds
  - mychips.creds_v
  - Translated all fields and function options
  - Used "credenciales" for "credentials" 
  - Translated function options: ausente, presente, más que, expresión regular
  - Used "puntuación" for "score" consistently

- Completed contracts-related tables/views
  - mychips.contracts
  - mychips.contracts_v
  - Translated all fields, messages, and UI instructions
  - Used "contrato" for "contract" consistently
  - Maintained established terminology, including "recuento" for "tally"
  - Preserved technical terms like "hash", "JSON", and "Base58"

- Completed agents-related tables/views
  - mychips.agents
  - mychips.agents_v
  - Translated all fields and error messages
  - Maintained consistent terminology for technical networking terms
  - Translated "Agent" as "Agente" consistently throughout
  - Used appropriate technical terms for networking concepts (socket, host, port)

- Completed routes-related tables/views
  - mychips.routes
  - mychips.routes_v
  - mychips.route_tries
  - Translated all fields with consistent terminology
  - Translated all status values in routes.status
  - Used "ruta" for "route" consistently
  - Maintained established terminology including "recuento" for "tally", "elevación" for "lift"
  - Used "intentos" for "tries" consistent with chit_tries translation

- Completed tallies views
  - mychips.tallies_v
  - mychips.tallies_v_me
  - Translated all fields in tallies_v with consistent terminology
  - Translated all nested state values in tallies_v.state
  - Used "Elevable" for "Liftable"
  - Maintained consistent terminology for "vale" (chit), "recuento" (tally), etc.
  - Skipped translation of deprecated mychips.tallies_v_sum view

### April 5, 2025
- Completed mychips.tallies
  - Added missing fields: revision, bound, closing, _last_chit
  - Added status.offer option
  - Added chain_stat nested options
  - Added all missing nested values for contract, hold_cert, hold_terms, and part_terms
  - Added missing messages: RCV, ISR
  - Improved translations for "clutch" (retención instead of embrague)
  - Improved translations for "foil" (contraparte instead of frustrar)
  - Improved translations for "digest" (resumen criptográfico instead of resumen de hachís)

- Completed mychips.users
  - Added missing field: _lift_check

- Completed all chits related tables/views
  - mychips.chits
  - mychips.chits_v
  - mychips.chits_v_me
  - mychips.chits_v_chains
  - mychips.chit_tries
  - Consistently used "vale" for "chit" across all objects
  - Used accounting terminology: "activo"/"pasivo" for asset/liability
  - Translated all nested state values and messages

- Completed all lifts related tables/views
  - mychips.lifts
  - mychips.lifts_v
  - mychips.lifts_v_me
  - mychips.lifts_v_dist
  - mychips.lifts_v_pay
  - mychips.lifts_v_pay_me
  - Consistently used "elevación" for "lift" across all objects
  - Translated all nested values and message texts
  - Added two views (lifts_v_pay and lifts_v_pay_me) that were found in the original file examination