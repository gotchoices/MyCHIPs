import jestExpect from 'expect';
//import Toast from 'react-native-toast-message';
//import notifee from '@notifee/react-native'

import { dbConf, testLog, dbClient, Format, getRow } from './utils/common';
import { getUrl } from './utils/connection';

let dbS;
let userO = 'p1000';
let userS = 'p1001';
const log = testLog(__filename);
const dbcS = new dbConf(log, `mu_${userS}`);

describe('Share and process tally', () => {
  beforeAll(async () => {
    const url = await getUrl(userO);
    await device.launchApp({
      url,
    });
  });

  beforeEach((done) => {
    dbS = new dbClient(dbcS, () => {
    }, async () => {
      done();
    })
  })

  afterEach(done => {
    dbS.disconnect();
    done();
  })

  it('should connect with the backend', async () => {
    await waitFor(element(by.text('Server Connected')))
      .toExist()
      .withTimeout(5000);
  });

  it('should create originator tally and process tally by subject', (done) => {
    const dbcO = new dbConf(log, `mu_${userO}`);
    const contract = { domain:"mychips.org", name:"deluxe", version:1.0 }
    let s1 = Format('insert into mychips.tallies_v (tally_ent, contract, comment) values(%L,%L,%L)', userO, contract, `Test ${new Date()}`)
      , sql = `with row as (${s1} returning tally_ent, tally_seq, ${'false'})
    insert into mychips.tokens (token_ent, tally_seq, reuse) select * from row returning *;
    select * from mychips.tallies_v where tally_ent = '${userO}' and tally_seq = 1;
    select token,expires,chad from mychips.tokens_v;`

    let dbO = new dbClient(dbcO, () => {
    }, async () => {
      dbO.query(sql, (e, res) => {
        if(e) {
          return done(e);
        }
        let ticket = res[2]?.rows?.[0] ?? {} 

        dbO.disconnect();
        let sql = Format('select mychips.ticket_process(%L,%L)', ticket, userS);

        dbS.query(sql, null, async (e, res) => {
          if (e) {
            console.log(e);
            done();
          }

          let row = getRow(res, 0)
          jestExpect(row.ticket_process).toBeTruthy();
          //jestExpect(notifee.displayNotification).toHaveBeenCalled();
          done();
        })
      })
    })
  })
});

describe('Offer tally to subject', () => {
  beforeEach((done) => {
    dbS = new dbClient(dbcS, () => {
    }, async () => {
      done();
    })
  })

  afterEach(done => {
    dbS.disconnect();
    done();
  })

  it('should connect with the backend', async () => {
    await waitFor(element(by.text('Server Connected')))
      .toExist()
      .withTimeout(5000);
  });

  it('should offer tally to the subject', async () => {
    await element(by.id('inviteBtn')).tap();
    await element(by.id('tally-0')).tap();
    await waitFor(element(by.id('offerBtn'))).toBeVisible().withTimeout(3000);
    await element(by.id('offerBtn')).tap();
  })
});

describe('Accept tally', () => {
  beforeAll(async () => {
    const url = await getUrl(userS);
    await device.launchApp({
      url,
      newInstance: true,
    });
  });

  it('should connect with the backend', async () => {
    await waitFor(element(by.text('Server Connected')))
      .toExist()
      .withTimeout(5000);
  });

  it('should accept tally by a subject', async () => {
    await element(by.id('inviteBtn')).tap();
    await element(by.id('tally-0')).tap();
    await waitFor(element(by.id('acceptBtn'))).toBeVisible().withTimeout(3000);
    await element(by.id('acceptBtn')).tap();
  })
});
