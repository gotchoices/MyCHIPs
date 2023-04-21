import { dbClient, dbConf, testLog } from '../../../../test/mocha/common';

const log = testLog(__filename);

export const getUrl = (user_id) => {
  const dbc = new dbConf(log, `mu_${user_id}`);

  return new Promise((resolve) => {
    let db;
    db = new dbClient(dbc, () => {}, () => {
      const sql = `select token, expires, host, port from base.ticket_login(base.user_id('${user_id}'))`
      db.query(sql, null, async (e, res) => {
        db.disconnect();
        if (e) {
          reject(e);
        }

        if (res && res.rows && res.rows.length >= 1) {
          let ticket = res.rows[0]
          let url = `https://mychips.org/connect?host\\\=${ticket.host}\\\&port\\\=${ticket.port}\\\&token\\\=${ticket.token}\\\&user\\\=${'p1000'}`;
          console.log('url', url)
          return resolve(url);
        }

        resolve('');
      })
    })
  });
}
