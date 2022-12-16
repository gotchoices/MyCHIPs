const Wm = require('../../src/wyseman');

let pktId = 1

export function query_user() {
  return new Promise((resolve, reject) => {
    Wm.request(pktId++, 'select', {
      view: 'base.ent_v',
      table: 'base.curr_eid',
      params: []
    }, data => {
      resolve(data);
    })
  })
}
