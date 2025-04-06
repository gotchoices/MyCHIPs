# Finnish (fin) Translation Status

Last synchronized with English: April 6, 2025

## Completion Status
✅ Finnish translation is now complete for all MyCHIPs schema components!

## Completed Schema Categories
- [x] MyCHIPs core schema tables and views (completed April 6, 2025)
- [x] JSON schema objects for API functionality (completed April 6, 2025)
- [x] Base schema objects (in mychips/../wyselib/schema/language/base-fin.wmt)
- [x] Wyseman schema objects (in mychips/../wyselib/schema/language/wm-fin.wmt)
- [x] UI-visible elements (chark, users_v_me, etc.)

## Completed Tables/Views

### Core MyCHIPs Schema
- [x] mychips.users and related views:
  - mychips.users, mychips.users_v, mychips.users_v_me, mychips.users_v_flat
  - mychips.users_v_tallies, mychips.users_v_tallies_me
  - mychips.users_v_tallysum (deprecated but translated)
  - mychips.addr_v_me, mychips.comm_v_me
- [x] mychips.tallies and related views:
  - mychips.tallies, mychips.tallies_v, mychips.tallies_v_me, mychips.tally_tries
  - mychips.tallies_v_net, mychips.tallies_v_edg, mychips.tallies_v_paths
  - mychips.tallies_v_sum (deprecated but translated)
- [x] mychips.chits and related views:
  - mychips.chits, mychips.chits_v, mychips.chits_v_me
  - mychips.chits_v_chains, mychips.chit_tries
- [x] mychips.lifts and related views:
  - mychips.lifts, mychips.lifts_v, mychips.lifts_v_me, mychips.lifts_v_dist
  - mychips.lifts_v_pay, mychips.lifts_v_pay_me
- [x] mychips.routes and related views:
  - mychips.routes, mychips.routes_v, mychips.route_tries
  - mychips.routes_v_paths, mychips.routes_v_query
- [x] mychips.agents and mychips.agents_v
- [x] mychips.contracts and mychips.contracts_v
- [x] mychips.creds and mychips.creds_v
- [x] mychips.tokens, mychips.tokens_v, mychips.tokens_v_me
- [x] mychips.file_v_me, mychips.file_v_part
- [x] mychips.chark (mobile app text elements)

### JSON Schema Objects
- [x] json.cert, json.connect, json.contract
- [x] json.file, json.place
- [x] json.tally, json.user, json.users

### Base Schema Objects (in wyselib/schema/language/base-fin.wmt)
- [x] base.addr, base.comm, base.ent
- [x] base.file, base.language, base.parm, base.priv

### Wyseman Schema Objects (in wyselib/schema/language/wm-fin.wmt)
- [x] wm.column_text, wm.message_text, wm.table_text, wm.value_text
- [x] wm.objects, wm.objects_v, wm.objects_v_depth, wm.objects_v_dep
- [x] wm.table_style, wm.column_style, wm.table_data, wm.column_data
- [x] wm.column_lang, wm.table_lang, wm.language, wm.releases

### Wylib Schema Objects (in wyselib/schema/language/wylib-fin.wmt)
- [x] wylib.data, wylib.data_v

## Terminology Decisions

### Core Domain Terminology
- "tally" -> "kirjanpito" (back-translation: "bookkeeping") - A record of transactions
- "chit" -> "tosite" (back-translation: "voucher") - A document proving a transaction
- "lift" -> "nosto" (back-translation: "withdrawal") - The act of transferring value in the network
- "stock" -> "varasto" (back-translation: "stock/inventory")
- "foil" -> "vastakappale" (back-translation: "counterpart")
- "circuit" -> "kiertopiiri" (back-translation: "circuit")
- "digest" -> "tiiviste" (back-translation: "digest/summary")
- "chain" -> "ketju" (back-translation: "chain")
- "referee" -> "välimies" (back-translation: "mediator/referee")

### General Terminology
- Technical terms maintained as-is: "CHIP", "GUI", "JSON", "UUID", etc.
- "user" -> "käyttäjä" (back-translation: "user")
- "view" -> "näkymä" (back-translation: "view")
- "entity" -> "entiteetti" (back-translation: "entity")
- "socket" -> "pistorasia" (back-translation: "socket")
- "status" -> "tila" (back-translation: "state/status")
- "access" -> "pääsy" (back-translation: "access")
- "private" -> "yksityinen" (back-translation: "private")
- "public" -> "julkinen" (back-translation: "public")
- "read" -> "lukea" (back-translation: "to read")
- "write" -> "kirjoittaa" (back-translation: "to write")
- "filter" -> "suodattaa" (back-translation: "to filter")
- "load" -> "ladata" (back-translation: "to load")
- "visible" -> "näkyvyys" (back-translation: "visibility")
- "preview" -> "esikatselu" (back-translation: "preview")
- "summary" -> "yhteenveto" (back-translation: "summary")

### Status Values
- "active" -> "aktiivinen" (back-translation: "active")
- "locked" -> "lukittu" (back-translation: "locked")
- "offline" -> "irrotettu" (back-translation: "disconnected")

## Terminology Consultation

For non-Finnish speakers reviewing this translation, here are the key terminology options considered:

### "tally" translation options:
- **"kirjanpito"** [chosen] - Back-translation: "bookkeeping" - A record of transactions
- **"laskelma"** - Back-translation: "calculation" or "estimate"
- **"tiliöinti"** - Back-translation: "accounting entry"

### "chit" translation options:
- **"tosite"** [chosen] - Back-translation: "voucher" - A document proving a transaction
- **"kuitti"** - Back-translation: "receipt" - A document showing a transaction

### "lift" translation options:
- **"nosto"** [chosen] - Back-translation: "withdrawal" or "lifting" (physical)
- **"siirto"** - Back-translation: "transfer"
- **"korotus"** - Back-translation: "raise" or "elevation"

### "stock/foil" translation options:
- **"varasto"** [chosen for stock] - Back-translation: "stock" or "inventory"
- **"vastakappale"** [chosen for foil] - Back-translation: "counterpart"

## File Location Notes
- Base schema definitions are found in mychips/../wyselib/schema/base/*.wmt
- Wyseman schema definitions are found in mychips/../wyseman/lib/run_time.wmt
- Translation files for non-MyCHIPs components are stored in mychips/../wyselib/schema/language/