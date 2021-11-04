//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
//Run all tests in order
const { DatabaseName, DBAdmin, MachineIP, Log } = require('../settings')
const { exec } = require('child_process')

require('./peercomm.js')
require('./objectset.js')
require('./peernoise.js')
require('./impexp.js')
require('./peer.js')

describe("At End", function() {

  it('Drop database: ' + DatabaseName, function(done) {
    exec('dropdb -U ' + DBAdmin + ' ' + DatabaseName)
    done()
  })
});
