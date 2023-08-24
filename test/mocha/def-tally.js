const Format = require('pg-format')
const {saveRest} = require('./common')

const stateField = 'mychips.tally_state(status,request,hold_sig,part_sig) as state'

module.exports = {
  stateField,
  sSql: (fields,...vals) => Format(`select ${fields} from mychips.tallies_v t join mychips.users_v u on u.id = t.tally_ent where t.tally_ent = %L and t.tally_seq = %s;`, ...vals),
  uSql: (sets,...vals) => Format(`update mychips.tallies set ${sets} where tally_ent = %L and tally_seq = %s returning *, ${stateField};`, ...vals),
  save: (tag) => saveRest(tag, 'mychips.tallies'),
  rest: (tag) => saveRest(tag, 'mychips.tallies', 'rest'),
}
