## MyChips 2025 Architecture Notes

### User Network for Lifts

- Replace the lift agent with a **user network**, a **libp2p Kademlia cluster** of computers.
- The network **may or may not include the user’s phone** and **may or may not include reliable cloud servers**.
- This network is **user-specific** and services lifts exclusively.

### Tally-Specific Network

- Replace the **current multi-tenant tally service** with a **tally-specific network**.
- The tally-specific network is a **libp2p cluster** composed of **nodes from both tally parties**.
- This **single network replaces the previous split-tally approach**, which required each user to sync a copy of the tally.
- A shared tally, where tally terms are visible to tally nodes for validation, helps prevent potential overspending scenarios.

### Establishing a Tally Network

- Each user **negotiates the initial set of nodes** that will constitute the tally network.
- Changes to the tally network can be **recorded as a ledger entry** signed by both parties.

### Database Storage and Optimystic Integration

- Each of these networks maintains **database tables** using the **Optimystic P2P database engine** (developed for VoteTorrent).
- The tally network utilizes a **transactional Diary** (append-only log) to store ledger entries.

### Network Bootstrapping and Coordination

- Each user is **furnished with bootstrap node addresses** for each tally partner, facilitating network access.
- **Inter-network communication** requires access to a **single coordinator node**, which acts on behalf of the network.
- **Consensus signatures** verify that the coordinator **did not act unilaterally**.

### Security and Key Management

- The two parties to a tally **negotiate a privately held key** to **encrypt sensitive tally information**.
- Each tally party also generates a **public key** for their next **user signed** action.
- Including the **next action’s key** in every action **creates a forward chain** without relying on old keys.

### Lift Transactions

- When a lift is propagated:
  - The **sending party records a conditional chit** (transaction entry) in the tally **before signing its promise** on the lift record.
  - The **receiving party signs its promise** only after **verifying the presence and correctness** of the conditional chit in the shared ledger.

### Partial-syncing Disconnected Devices

- If one or both parties are **disconnected from the tally network** but have a **direct device connection**, they can:
  - **Share pending transactions** between devices.
  - **Final transactions require network consensus**.
  - Logical and physical transactions can be **sent from one device to another**.
  - When either party **reconnects to the network**, syncing resumes and progresses.

### Cloud and Node Marketplace

- On signup, **cloud nodes** could be offered to create or extend a user’s network.
- A **node marketplace** could also be established to create an infrastructure marketplace.

