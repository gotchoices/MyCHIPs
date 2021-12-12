//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
//Run all tests in order
const { DatabaseName, DBAdmin, MachineIP, Log } = require('../settings')
const { exec } = require('child_process')

require('./objectset.js')
require('./peernoise.js')

require('./peercomm.js')	//Deprecated

require('./impexp.js')		//Will add users needed for peer test
require('./peer.js')

require('./schema.js')		//Will empty users table

describe("At End", function() {

  it('Drop database: ' + DatabaseName, function(done) {
    exec('dropdb -U ' + DBAdmin + ' ' + DatabaseName)
    done()
  })
});
