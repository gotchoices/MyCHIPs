const Format = require('pg-format')
const {saveRest} = require('./common')

const stateField = 'mychips.tally_state(status,request,hold_sig,part_sig) as state'

module.exports = {
  stateField,
  uSql: (sets,...vals) => Format(`update mychips.tallies set ${sets} where tally_ent = %L and tally_seq = %s returning *, ${stateField};`, ...vals),
  save: (tag) => saveRest(tag, 'mychips.tallies'),
  rest: (tag) => saveRest(tag, 'mychips.tallies', 'rest'),
}
