import Action from "../action";
import Account from "../account";
import AccountCache from "../accountsCache";
import MongoManager from "../mongomanager";
import SQLManager from "../sqlmanager";
import UnifiedLogger from "../unifiedLogger";

class FindNewSpendingTarget implements Action{
	logger: WyclifLogger
	myChipsDBManager: SQLManager
	worldDBManager: MongoManager
	accountCache: AccountCache
	account: Account
	
	constructor(account: Account) {
		this.logger = UnifiedLogger.getInstance()
		this.myChipsDBManager = SQLManager.getInstance()
		this.worldDBManager = MongoManager.getInstance()
		this.accountCache = AccountCache.getInstance()

		this.account = account
	}

	run() {        
		if (this.account.numSpendingTargets <= 0 ||                 // If the account has no stocks   or
			(this.account.numSpendingTargets < this.account.maxSpendingTargets &&   // (if the account doesn't have too many stocks and
				Math.random() < this.account.newSpendingTargetOdds))       //  we randgomly choose to))
		{
			console.log("\n", this.account.peer_cid, "is finding a new spending target!")
			this.worldDBManager.findPeerAndUpdate(this.account.peer_cid, this.account.spendingTargetCids, (newPeer: AccountData) => {
				console.log(this.account.peer_cid, "wants to connect to", newPeer.peer_cid)
				console.log("Peer from mongo:", newPeer.peer_cid, newPeer.id, "on", newPeer.peer_sock.split(':')[0])

				this.logger.debug(this.account.peer_cid, "  attempting new spending source with", newPeer.peer_cid)

				// TODO: Clean this up...
				if (!this.accountCache.containsAccount(newPeer)) {
					this.myChipsDBManager.addPeerAccount(newPeer, (newLocalPeer) => {
						console.log("Peer", newLocalPeer.peer_cid, "now has id:", newLocalPeer.id)
						// See if the peer is on a different server
						let newPeerServer = newLocalPeer.peer_sock.split(':')[0]
						if (newPeerServer != this.account.host) {
							// If it is, request that the other server gets our info
							this.worldDBManager.insertAction("createAccount", undefined, newPeerServer, this.account.getAccountData(), () => {
								this.addConnection(newLocalPeer.id, newLocalPeer.peer_cid)
							})
						}
						else {
							// Otherwise, just made the connection request
							this.addConnection(newLocalPeer.id, newLocalPeer.peer_cid)
						}
					})
				}
				else {
					newPeer = this.accountCache.getAccountByCID(newPeer.peer_cid)
					let newPeerServer = newPeer.peer_sock.split(':')[0]
					if (newPeerServer != this.account.host) {
						// If it is, request that the other server gets our info
						this.worldDBManager.insertAction("createAccount", undefined, newPeerServer, this.account.getAccountData(), () => {
							this.addConnection(newPeer.id, newPeer.peer_cid)
						})
					}
					else {
						// Otherwise, just made the connection request
						this.addConnection(newPeer.id, newPeer.peer_cid)
					}
				}
			})
		}
	}

	addConnection(peer_id: string, peer_cid: string) {
		console.log(this.account.peer_cid, "(", this.account.id, ") sending connection request to", peer_cid, "(", peer_id, ")")
		this.myChipsDBManager.addConnectionRequest(this.account.id, peer_id)
		this.account.numSpendingTargets++
		if (!this.account.spendingTargetCids.includes(peer_cid)) {
			console.log(this.account.peer_cid, "is adding", peer_cid, "to their lists")
			this.account.spendingTargets.push(peer_id)
			this.account.spendingTargetCids.push(peer_cid)
		}
		console.log(this.account.peer_cid, "now has", this.account.numSpendingTargets, "spending targets:\n",
			this.account.spendingTargetCids)
		this.worldDBManager.updateOneAccount(this.account.getAccountData())
	}
}

export default FindNewSpendingTarget;