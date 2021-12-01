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

// Establishes a new Tally with a new agent found in the worldDB
const MakeNewTally = function(agentData, parameters, worldDBFacade, myChipsDBFacade, checkForPeer, remoteCall, logger) {

  this.shouldProcess = function() {
    return agentData.stocks <= 0 ||                 // If the agent has no stocks   or
      (agentData.stocks < parameters.maxstocks &&   // (if the agent doesn't have too many stocks and
        Math.random() < parameters.addclient)       //  we randgomly choose to)
  }

  this.process = function() {
    //FIXME: This stuff should be put in the MongoDB Facade!
    worldDBFacade.findPeerAndUpdate(agentData, parameters, tryTally);

    /* This is the method that the facade will call on MongoDB (SHOULD BE MOVED TO OTHER CLASS!)
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
    // ---- End Stuff to put in MongoDB Manager */
  }

  // Try to request tally from someone in the world
  var tryTally = function(agentData, peerWorldData) {

    logger.debug("  Try tally:", agentData.peer_cid, 'with', peerWorldData.peer_cid)

    checkForPeer(peerWorldData, (peerHostData, hadEm) => {
      let host = peerHostData.peer_sock.split(':')[0]
      
      remoteCall(host, 'createUser', agentData, () => {	//Insert this peer remotely    
        logger.debug("Tally request:", tallySql, aData.id, peerHostData.id)

        // Adds a tally to the HostDB
        myChipsDBFacade.addTally(agentData, peerHostData)

        /* ---- This is what the facade will call on the SQLDB (SHOULD BE MOVED TO OTHER CLASS!)
        let guid = uuidv4()
        let sig = "Valid"
        let contract = {name: "mychips-0.99"}
        let tallySql = "insert into mychips.tallies_v (tally_ent, tally_guid, partner, user_sig, contract, request) values ($1, $2, $3, $4, $5, $6);"
        let partner = 'test'
        this.sqlDB.query(tallySql, [aData.id, guid, peerHostData.id, sig, contract, 'draft'], (err,res) => {
          if (err) {this.log.error('In query:', err.stack); return}
          this.log.debug("  Initial tally by:", aData.std_name, " with partner:", peerHostData.std_name)
          aData.stocks++
          // pData.foils++
        })
        // ---- End Stuff to put in SQLDB manager */
      })
    })
  }
}


// Pays a Vendor some CHIPs
const PayVendor = function(agentData, parameters, worldDBFacade, myChipsDBFacade, getAgentInfo, logger) {

  this.shouldProcess = function() {
    return agentData.foils > 0 && agentData.units > parameters.mintopay
  }

  this.process = function() {
    let vendorIdx = Math.floor(Math.random() * agentData.foils)
    let vendorId = agentData.vendors[vendorIdx]
    let vendorData = getAgentInfo(vendorId)

    if (vendorData) {
      logger.debug("  I:", aData.id, "; Pay a vendor", vendorIdx, 'of', aData.vendors.length, vendorId, "NW:", aData.units)

      // Ask the MyCHIPsDB to make the payment
      myChipsDBFacade.payVendor(agentData, vendorIdx, vendorData)
      // I think the AgentCluster is listening to the MyCHIPsDB, so when this change is made,
      // it detects the change and updates the WorldDB accordingly.

      /* This is what the SQLDB facade should implement (SHOULD BE MOVED TO OTHER CLASS!)
      let guid = uuidv4()
      , sig = "Valid"
      , max = Math.max(agentData.units * this.parms.maxtopay, 1000)		//Pay 1 CHIP or % of net worth
      , units = Math.floor(Math.random() * max)
      , seq = agentData.foil_seqs[vendorIdx]			//Tally sequence
      , quid = 'Inv' + Math.floor(Math.random() * 1000)
      , req = 'userDraft'
      , sql = "insert into mychips.chits_v (chit_ent,chit_seq,chit_guid,chit_type,signature,units,quidpro,request) values ($1,$2,$3,'tran',$4,$5,$6,$7)"

      this.log.verbose("  payVendor:", agentData.id, "->", vendorData.id, "on:", seq, "Units:", units)
      this.sqlDB.query(sql, [agentData.id,seq,guid,sig,units,quid,req], (e,r) => {
        if (e) {this.log.error('In payment:', e.stack); return}
        this.log.debug("  payment:", agentData.id, agentData.std_name, "to:", vendorData.id, vendorData.std_name)
      })
      // End of stuff to move to DB manager */
    }
  }
}

// ---------------- Add new Action Definitions here ------------------------ \\

export default {
  MakeNewTally,
  PayVendor
  // Add new actions here
}
