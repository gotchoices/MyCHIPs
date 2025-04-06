# Finnish (fin) Translation Status

Last synchronized with English: April 6, 2025

## Next Priority Tasks
- [ ] Create mychips/../wyselib/schema/language/base-fin.wmt for Base schema objects (based on mychips/../wyselib/schema/base/*.wms)
- [ ] Create mychips/../wyselib/schema/language/wm-fin.wmt for Wyseman schema objects (based on mychips/../wyseman/lib/run_time.wmt)
- [ ] Complete the core MyCHIPs schema tables (tallies, chits, lifts)
- [ ] Complete json schema objects for API functionality

## Completed Tables/Views
- [x] mychips.users (partial translation)
- [x] mychips.users_v (partial translation)
- [x] wylib.data (partial translation, in wyselib/schema/language/wylib-fin.wmt)

## In Progress
None currently - waiting for prioritization of schema objects for translation.

## Pending Translation Audit

### MyCHIPs Schema
- [ ] mychips.addr_v_me
- [ ] mychips.agents
- [ ] mychips.agents_v
- [ ] mychips.chark
- [ ] mychips.chits
- [ ] mychips.chits_v
- [ ] mychips.chits_v_chains
- [ ] mychips.chits_v_me
- [ ] mychips.chit_tries
- [ ] mychips.contracts
- [ ] mychips.contracts_v
- [ ] mychips.creds
- [ ] mychips.creds_v
- [ ] mychips.file_v_me
- [ ] mychips.file_v_part
- [ ] mychips.lifts
- [ ] mychips.lifts_v
- [ ] mychips.lifts_v_dist
- [ ] mychips.lifts_v_me
- [ ] mychips.lifts_v_pay
- [ ] mychips.lifts_v_pay_me
- [ ] mychips.routes
- [ ] mychips.routes_v
- [ ] mychips.routes_v_paths
- [ ] mychips.routes_v_query
- [ ] mychips.route_tries
- [ ] mychips.tallies
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

### JSON Schema Objects
- [ ] json.cert
- [ ] json.connect
- [ ] json.contract
- [ ] json.file
- [ ] json.place
- [ ] json.tally
- [ ] json.user
- [ ] json.users

### Wylib Schema Objects
Note: The following objects are found in mychips/../wyselib/schema/language/wylib-fin.wmt
- [ ] wylib.data (complete the remaining fields)
- [ ] wylib.data_v

### Base Schema Objects
Note: Base schema definitions are found in mychips/../wyselib/schema/base/*.wms
Translation files should be placed in mychips/../wyselib/schema/language/base-fin.wmt
- [ ] base.addr
- [ ] base.comm
- [ ] base.ent
- [ ] base.file
- [ ] base.language
- [ ] base.parm
- [ ] base.priv

### Wyseman Schema Objects
Note: Wyseman schema definitions are found in mychips/../wyseman/lib/run_time.wmt
Translation files should be placed in mychips/../wyselib/schema/language/wm-fin.wmt
- [ ] wm.column_text
- [ ] wm.message_text
- [ ] wm.objects
- [ ] wm.objects_v
- [ ] wm.table_text
- [ ] wm.value_text

## Specific Translation Notes for Finnish

## Translation Decisions and Terminology

The following terminology decisions have been implemented:
- "CHIP" remains "CHIP" (not translated)
- "user" -> "käyttäjä" (back-translation: "user")
- "view" -> "näkymä" (back-translation: "view")
- "entity" -> "entiteetti" (back-translation: "entity")
- "socket" -> "pistorasia" (back-translation: "socket")
- "status" -> "tila" (back-translation: "state" or "status")
- "active" -> "aktiivinen" (back-translation: "active")
- "locked" -> "lukittu" (back-translation: "locked")
- "offline" -> "irrotettu" (back-translation: "disconnected")
- "GUI" remains "GUI" (not translated)
- "component" -> "komponentti" (back-translation: "component")
- "access" -> "pääsy" (back-translation: "access")
- "private" -> "yksityinen" (back-translation: "private")
- "public" -> "julkinen" (back-translation: "public")
- "read" -> "lukea" (back-translation: "to read")
- "write" -> "kirjoittaa" (back-translation: "to write")
- "filter" -> "suodattaa" (back-translation: "to filter")
- "load" -> "ladata" (back-translation: "to load")
- "reload" -> "ladata" (back-translation: "to load")
- "visible" -> "näkyvyys" (back-translation: "visibility")
- "preview" -> "esikatselu" (back-translation: "preview")
- "summary" -> "yhteenveto" (back-translation: "summary")

## Terminology Consultation

For non-Finnish speakers reviewing this translation, here are questions about key terminology:

### "tally" translation options:
- **"kirjanpito"** - Back-translation: "bookkeeping" - A record of transactions
- **"laskelma"** - Back-translation: "calculation" or "estimate"
- **"tiliöinti"** - Back-translation: "accounting entry"

### "chit" translation options:
- **"kuitti"** - Back-translation: "receipt" - A document showing a transaction
- **"tosite"** - Back-translation: "voucher" - A document proving a transaction

### "lift" translation options:
- **"nosto"** - Back-translation: "withdrawal" or "lifting" (physical)
- **"siirto"** - Back-translation: "transfer"
- **"korotus"** - Back-translation: "raise" or "elevation"

## Prioritization Plan

First priority:
1. Complete MyCHIPs core tables (tallies, chits, lifts)
2. Focus on UI-visible elements (chark, users_v_me)
3. Complete json schema for API functionality
4. Fill in remaining wylib components
5. Add base and wyseman schema translations

## Completed Translations

### Initial Work (Pre-April 2025)
- Basic translation of mychips.users with status values
- Basic translation of mychips.users_v
- Partial translation of wylib.data with key UI elements