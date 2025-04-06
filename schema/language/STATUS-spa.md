# Spanish (spa) Translation Status

Last synchronized with English: April 6, 2025

## Completion Status
✅ Spanish translation is now complete for all MyCHIPs schema components!

## Completed Schema Categories
- [x] MyCHIPs core schema tables and views (completed April 6, 2025)
- [x] JSON schema objects for API functionality (completed April 6, 2025)
- [x] Base schema objects (in mychips/../wyselib/schema/language/base-spa.wmt)
- [x] Wyseman schema objects (in mychips/../wyselib/schema/language/wm-spa.wmt)
- [x] UI-visible elements (chark, users_v_me, etc.)

## Completed Tables/Views

### Core MyCHIPs Schema
- [x] mychips.users and related views:
  - mychips.users, mychips.users_v, mychips.users_v_me, mychips.users_v_flat
  - mychips.users_v_tallies, mychips.users_v_tallies_me, mychips.users_v_tallysum
  - mychips.addr_v_me, mychips.comm_v_me
- [x] mychips.tallies and related views:
  - mychips.tallies, mychips.tallies_v, mychips.tallies_v_me, mychips.tally_tries
  - mychips.tallies_v_net, mychips.tallies_v_edg, mychips.tallies_v_paths
  - mychips.tallies_v_sum (deprecated - no translation needed)
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

### Base Schema Objects (in wyselib/schema/language/base-spa.wmt)
- [x] base.addr, base.comm, base.ent
- [x] base.file, base.language, base.parm, base.priv

### Wyseman Schema Objects (in wyselib/schema/language/wm-spa.wmt)
- [x] wm.column_text, wm.message_text, wm.table_text, wm.value_text
- [x] wm.objects, wm.objects_v
- [x] Plus additional Wyseman schema objects

### Wylib Schema Objects (in wyselib/schema/language/wylib-spa.wmt)
- [x] wylib.data, wylib.data_v

## Terminology Decisions

### Core Domain Terminology
- "tally" -> "recuento" (back-translation: "count" or "tally")
- "chit" -> "vale" (back-translation: "voucher" or "receipt")
- "lift" -> "elevación" (back-translation: "elevation" or "raising")
- "stock" -> "existencias" (back-translation: "stock" or "inventory")
- "foil" -> "contraparte" (back-translation: "counterpart")
- "clutch" -> "retención" (back-translation: "retention")
- "digest" -> "resumen criptográfico" (back-translation: "cryptographic summary")
- "circuit" -> "circuito" (back-translation: "circuit")
- "asset" -> "activo" (back-translation: "asset" - standard financial term)
- "liability" -> "pasivo" (back-translation: "liability" - standard financial term)

### Network Terminology
- "route" -> "ruta" (back-translation: "route" or "path")
- "pathway" -> "vía" (back-translation: "way" or "path")
- "edge" -> "enlace" (back-translation: "link")
- "node" -> "nodo" (back-translation: "node")
- "tries" -> "intentos" (back-translation: "attempts" or "tries")
- "lading" -> "cargamento" (back-translation: "cargo" or "shipment")

### General Terminology
- Technical terms maintained as-is: "CHIP", "GUI", "JSON", "UUID", "token", "hash"
- "contract" -> "contrato" (back-translation: "contract")
- "section" -> "sección" (back-translation: "section")
- "credentials" -> "credenciales" (back-translation: "credentials")
- "file" -> "archivo" (back-translation: "file")
- "media" -> "medio" (back-translation: "medium")
- "agent" -> "agente" (back-translation: "agent")
- "peer" -> "par" or "igual" (back-translation: "peer" or "equal")

## Terminology Consultation

For non-Spanish speakers reviewing this translation, here are the key terminology options considered:

### "chit" translation options:
- **"vale"** [chosen] - Back-translation: "voucher" or "receipt" - A document representing value or credit
- **"nota"** - Back-translation: "note" - A record of something owed

Update: "Vale" better conveys a formal record of value that can be redeemed, fitting the historical concept of a notch in a tally stick.

### "foil" translation options:
- **"contraparte"** [chosen] - Back-translation: "counterpart" - The opposing part in a relationship
- **"frustrar"** [original translation] - Back-translation: "to frustrate" - This was incorrect in context

### "clutch" translation options:
- **"retención"** [chosen] - Back-translation: "retention" - The action of keeping or maintaining
- **"agarre"** [previous choice] - Back-translation: "grip" - More of a verb form or action of gripping
- **"embrague"** [original translation] - Back-translation: "mechanical clutch" - A mechanical device

### "lift" translation options:
- **"elevación"** [chosen] - Back-translation: "elevation" or "raising" - The act of moving something upward
- **"levantamiento"** - Back-translation: "lifting" - Similar meaning but longer word
- **"alza"** - Back-translation: "rise" - Could work but less precise

## Translation Improvements
- Changed "foil" from "frustrar" to "contraparte"
- Changed "digest" from "resumen de hachís" to "resumen criptográfico"
- Changed "clutch" from "embrague" to "retención"

## File Location Notes
- Base schema definitions are found in mychips/../wyselib/schema/base/*.wmt
- Wyseman schema definitions are found in mychips/../wyseman/lib/run_time.wmt
- Translation files for non-MyCHIPs components are stored in mychips/../wyselib/schema/language/