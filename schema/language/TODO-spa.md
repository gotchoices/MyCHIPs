# Spanish (spa) Translation Progress

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
- [ ] mychips.addr_v_me
- [ ] mychips.agents
- [ ] mychips.agents_v
- [ ] mychips.chark
- [ ] mychips.contracts
- [ ] mychips.contracts_v
- [ ] mychips.creds
- [ ] mychips.creds_v
- [ ] mychips.file_v_me
- [ ] mychips.file_v_part
- [ ] mychips.route_tries
- [ ] mychips.routes
- [ ] mychips.routes_v
- [ ] mychips.routes_v_paths
- [ ] mychips.routes_v_query
- [ ] mychips.tallies_v
- [ ] mychips.tallies_v_edg
- [ ] mychips.tallies_v_me
- [ ] mychips.tallies_v_net
- [ ] mychips.tallies_v_paths
- [ ] mychips.tallies_v_sum
- [ ] mychips.tally_tries
- [ ] mychips.tokens
- [ ] mychips.tokens_v
- [ ] mychips.tokens_v_me
- [ ] mychips.users_v_flat
- [ ] mychips.users_v_me
- [ ] mychips.users_v_tallies
- [ ] mychips.users_v_tallies_me
- [ ] mychips.users_v_tallysum

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
- "token" -> "token" (no translation - technical term kept as-is)
- "agent" -> "agente" (back-translation: "agent")
- "peer" -> "par" or "igual" (back-translation: "peer" or "equal")

## Completed Translations

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