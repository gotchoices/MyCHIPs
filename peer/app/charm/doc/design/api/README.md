# MyCHIPs Mobile App API Specification

*API procedure calls and data schemas for the MyCHIPs peer-to-peer credit system mobile application*

## 🏗️ Architecture Context

### **Technology Stack**
- **quereus** → SQL query abstraction layer
- **optimystic** → Optimistic conflict resolution
- **kademlia** → Distributed hash table for peer discovery
- **libp2p** → Peer-to-peer networking protocol

### **Database Architecture**
- **Per-tally SQL databases** - Each tally relationship maintains its own database instance
- **Local private database** - User's personal data (identity, preferences, onboarding state)
- **Distributed synchronization** - Tally data synchronized between partners via p2p protocols

### **Engine Responsibilities**
The MyCHIPs engine converts API procedure calls to appropriate SQL operations across:
1. **Local database queries** (user profile, settings, local state)
2. **Tally-specific database queries** (partner transactions, credit balances)
3. **P2P network operations** (partner discovery, invitation sending)
4. **Cross-tally aggregations** (total balance calculations, activity summaries)

## 📱 API Design Philosophy

### **Procedure Call Interface**
Unlike REST APIs, the mobile app communicates with the engine through direct procedure calls:
```javascript
// Direct procedure calls (not HTTP endpoints)
const balance = await balance.getSummary();
const result = await tally.create({ partnerId, creditLimits });
const transactions = await transaction.getRecent({ limit: 10 });
```

### **Data Flow Patterns**
1. **Read Operations** - Query local DB first, then tally DBs, aggregate results
2. **Write Operations** - Update local state, propagate to relevant tally DBs via p2p
3. **Real-time Updates** - Subscribe to changes across distributed databases
4. **Conflict Resolution** - Handle optimystic conflicts when tally data diverges

### **Mock Layer Strategy**
During development, mock implementations provide:
- **Static data** for initial UI development
- **Interactive scenarios** for user flow testing  
- **Error simulation** for edge case handling
- **Performance testing** with large datasets

The same API calls work with mocks or the real distributed engine.

## 📁 Directory Structure

```
api/
├── README.md              # This file - architecture and guidelines
├── procedures/            # API procedure definitions by functional area
│   ├── auth.md           # User authentication and identity management
│   ├── balance.md        # Balance queries and aggregations
│   ├── transactions.md   # Transaction history and operations
│   ├── tallies.md        # Tally relationship management
│   ├── onboarding.md     # Getting started flows and tutorials
│   └── sync.md           # P2P synchronization and conflict resolution
├── schemas/              # Data models and type definitions
│   ├── core-types.yaml   # Fundamental data types (User, Tally, Transaction)
│   ├── database-schema.yaml # SQL table structures for local and tally DBs
│   ├── network-messages.yaml # P2P message formats
│   └── api-responses.yaml # Procedure call response formats
├── mock/                 # Mock implementations for development
│   ├── README.md         # Mock layer documentation
│   ├── data/             # Static mock datasets
│   ├── procedures.js     # Mock procedure implementations
│   └── scenarios/        # User story scenario data
└── examples/             # Real-world usage examples and test cases
    ├── user-flows/       # Complete user journey API call sequences
    ├── error-cases/      # Error handling and edge case examples
    └── performance/      # Load testing and optimization examples
```

## 🎯 API Requirements from Current Design

### **Screens Requiring API Support**
Based on our completed screen designs, the API must support:

1. **App Launch** (`app-launch.xml`)
   - User identity verification
   - Onboarding state management
   - Initial data synchronization

2. **Identity Setup** (`identity-setup.xml`)
   - Profile creation and updates
   - Identity verification
   - Key generation and storage

3. **Home Dashboard** (`home-dashboard.xml`)
   - Balance aggregation across all tallies
   - Recent transaction history
   - Getting started task management
   - Real-time balance updates

4. **Tally Management** (`tally-review.xml`, `tally-templates.xml`)
   - Tally relationship creation
   - Partner search and discovery
   - Credit limit negotiation
   - Template management

6. **QR Code Sharing** (`qr-share.xml`)
   - Invitation URL generation
   - QR code creation for tally invitations
   - Deep link handling

### **User Stories Driving API Design**
Our completed user stories reveal specific API requirements:

- **Discovery-Driven Onboarding** → Profile management, task tracking, external web content access
- **First Friend Tally** → Partner search, tally creation, invitation sending
- **Email Tally Response** → Invitation processing, tally acceptance, partner verification

## 🔧 Development Workflow

### **API-First Design Process**
1. **User story analysis** → Extract required data operations
2. **Screen design review** → Identify data attributes and user actions
3. **Procedure definition** → Specify API calls with parameters and responses
4. **Schema creation** → Define data structures for distributed SQL storage
5. **Mock implementation** → Build interactive mocks for UI development
6. **Integration testing** → Validate API calls with real distributed engine

### **Mock-to-Engine Transition**
The API design supports seamless transition from development mocks to production engine:
```javascript
// Same code works with mocks or real engine
const api = process.env.NODE_ENV === 'development' 
  ? createMockApi(scenario) 
  : createEngineApi(engineInstance);

// Identical procedure calls
const balance = await api.balance.getSummary();
```

### **Testing Strategy**
- **Unit tests** → Mock individual procedure calls
- **Integration tests** → Test complete user flows with realistic data
- **Performance tests** → Validate behavior with large tally networks
- **Conflict resolution tests** → Simulate distributed database conflicts

## 🚀 Next Steps

### **Phase 1: Core Procedures** (Current)
Define API procedures for existing screens and user stories:
- Authentication and identity management
- Balance calculations and transaction history
- Tally creation and management
- Marketplace vendor discovery

### **Phase 2: Advanced Features**
Expand API for additional user stories:
- Payment processing and settlement
- Advanced tally negotiations
- Offline operation support
- Security and backup features

### **Phase 3: Optimization**
Performance and scalability improvements:
- Caching strategies for distributed data
- Optimistic UI updates
- Background synchronization
- Network-aware data loading

---

*This API specification ensures the mobile app can efficiently interact with the distributed MyCHIPs engine while maintaining clean separation between UI logic and backend complexity.*
