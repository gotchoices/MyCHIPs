const Format = require('pg-format')
const {saveRest} = require('./common')

//Query state without having access to chits_v
//const stateField = `mychips.chit_state((
//    select tally_type = 'stock' and mychips.chits.units >= 0 or tally_type = 'foid' and mychips.chits.units < 0 
//    from mychips.tallies
//    where tally_ent = mychips.chits.chit_ent and tally_seq = mychips.chits.chit_seq
//  ), status, request) as state`

module.exports = {
//  stateField,
//  uSql: (sets,...vals) => Format(`update mychips.chits set ${sets} where chit_ent = %L and chit_uuid = %L returning *, ${stateField};`, ...vals),
  uSql: (sets,...vals) => Format(`update mychips.chits_v set ${sets} where chit_ent = %L and chit_uuid = %L returning *;`, ...vals),
  save: (tag) => saveRest(tag, 'mychips.chits'),
  rest: (tag) => saveRest(tag, 'mychips.chits', 'rest'),
}
