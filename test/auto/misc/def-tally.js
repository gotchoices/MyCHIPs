const Format = require('pg-format')
const {saveRest} = require('../common')

module.exports = {
  sSql: (fields,...vals) => Format(`select ${fields} from mychips.tallies_v t join mychips.users_v u on u.id = t.tally_ent where t.tally_ent = %L and t.tally_seq = %s;`, ...vals),
  uSql: (sets,...vals) => Format(`update mychips.tallies t set ${sets} where tally_ent = %L and tally_seq = %s returning *, mychips.tally_state(t) as state;`, ...vals),
  save: (tag) => saveRest(tag, 'mychips.tallies'),
  rest: (tag) => saveRest(tag, 'mychips.tallies', 'rest'),
}
