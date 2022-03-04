//const Format = require('pg-format')
const {saveRest} = require('./common')

//const stateField = 'mychips.route_state() as state'

module.exports = {
//  stateField,
//  uSql: (sets,...vals) => Format(`update mychips.routes set ${sets} where tally_ent = %L and tally_seq = %s returning *, ${stateField};`, ...vals),
  save: (tag) => saveRest(tag, 'mychips.routes'),
  rest: (tag) => saveRest(tag, 'mychips.routes', 'rest'),
}
