const Format = require('pg-format')
const {saveRest} = require('../common')

module.exports = {
//  uSql: (sets,...vals) => Format(`update mychips.chits set ${sets} where chit_ent = %L and chit_uuid = %L returning *, ${stateField};`, ...vals),
  sSql: (fields,...vals) => Format(`select ${fields} from mychips.chits_v c join mychips.users_v u on u.id = c.chit_ent where c.chit_ent = %L and c.chit_uuid = %L;`, ...vals),
  uSql: (sets,...vals) => Format(`update mychips.chits_v set ${sets} where chit_ent = %L and chit_uuid = %L returning *;`, ...vals),
  save: (tag) => saveRest(tag, 'mychips.chits'),
  rest: (tag) => saveRest(tag, 'mychips.chits', 'rest'),
}
