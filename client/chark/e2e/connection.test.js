import { dbConf, testLog, dbClient } from '../../../test/mocha/common';
import { getUrl } from './utils/connection';

const log = testLog(__filename);
const dbcS = new dbConf(log, 'mu_p1001');
let dbS;

describe('Token connection', () => {
  beforeAll(async () => {
    const url = await getUrl('p1000');
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
    //await element(by.id('serverIcon')).tap();
    //await waitFor(element(by.id('debugModal'))).toBeVisible().withTimeout(3000);
    //await element(by.id('connectWithToken')).tap();
    //await element(by.id('cancelButton')).tap();

    await waitFor(element(by.text('Server Connected')))
      .toExist()
      .withTimeout(5000);
  });
});
