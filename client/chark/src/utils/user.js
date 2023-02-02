
let pktId = 1

export function query_user(wm) {
  return new Promise((resolve, reject) => {
    wm.request(pktId++, 'select', {
      view: 'base.ent_v',
      table: 'base.curr_eid',
      params: []
    }, data => {
      resolve(data);
    })
  })
}
