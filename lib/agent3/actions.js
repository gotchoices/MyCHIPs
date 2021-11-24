/* 
All Action functions should follow this pattern! Treat it like an interface.
const Action = (needed parameters) => {
  this.shouldProcess = () => {
    // conditions for processing the actions
    // returns true or false
  }

  this.process = () => {
    // perform the action!
  }

  var privateHelperFunction = (args...) => {
    ...
  }
}
*/

const MakeNewTally = function(agentData, worldDBFacade, myChipsDBFacade, logger) {
  this.agentData = agentData
  this.worldDBFacade = worldDBFacade
  this.myChipsDBFacade = myChipsDBFacade
  this.logger = logger

  this.shouldProcess = function() {
    return agentData.stocks <= 0 ||                 // If the agent has no stocks   or
      (agentData.stocks < this.parms.maxstocks &&   // (if the agent doesn't have too many stocks and
        Math.random() < this.parms.addclient)       //  we randgomly choose to)
  }

  this.process = function() {
    //FIXME: This stuff should be put in the MongoDB Facade!
    worldDBFacade.findPeerAndUpdate(agentData, tryTally);

    // This is the method that the facade will call on MongoDB
    agentCollection.findOneAndUpdate(     // Look for a new trading partner
      {   // Filter Options 
        peer_cid: {
          $ne: agentData.peer_cid,				// Don't find myself
          $nin: agentData.partners				// or anyone I'm already connected to
        },
        foils: {
          $lte: parameters.maxfoils       // Don't find others with too many foils already
        }
      },
      {   // Update Operations
        $set: {random: Math.random()},	  // Re-randomize this agent
        $inc: {foils: 1},				          // Update how many foils they have
        $push: {partners: agentData.peer_cid}	// Immediately add ourselves to their peer array to avoid double connecting
      },
      {   // Optional Settings
        sort: {
          foils: 1,                       // Sort by number of foils
          random: -1                      // and random value
        }
      },
      (err, res) => {   // Callback Function
        if (err) {
          logger.error(err.errmsg)
        } else if (res.ok) {
          tryTally(agentData, res.value)
        } else {
          logger.verbose("  No peer found in World DB")
        }
      }
    )
  }

  // Try to request tally from someone in the world
  var tryTally = function(agentData, peerWorldData) {

    logger.debug("  Try tally:", agentData.peer_cid, 'with', peerWorldData.peer_cid)

    this.checkPeer(peerWorldData, (peerHostData, hadEm) => {
      let host = pDoc.peer_sock.split(':')[0]
      this.remoteCall(host, 'createUser', aData, () => {	//Insert this peer remotely
        let guid = uuidv4()
          , sig = "Valid"
          , contract = {name: "mychips-0.99"}
          , tallySql = "insert into mychips.tallies_v (tally_ent, tally_guid, partner, user_sig, contract, request) values ($1, $2, $3, $4, $5, $6);"
          , partner = 'test'
    
        this.log.debug("Tally request:", tallySql, aData.id, peerHostData.id)
        this.sqlDB.query(tallySql, [aData.id, guid, peerHostData.id, sig, contract, 'draft'], (err,res) => {
          if (err) {this.log.error('In query:', err.stack); return}
          this.log.debug("  Initial tally by:", aData.std_name, " with partner:", peerHostData.std_name)
          aData.stocks++
          // pData.foils++
        })
      })
    })
  }
}

module.exports = {
  MakeNewTally
}
