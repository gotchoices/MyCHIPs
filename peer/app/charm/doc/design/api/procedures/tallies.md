# Tally Relationship Management API

*Tally creation, partner discovery, credit negotiation, and relationship management procedures*

## 🏗️ Database Context

### **Distributed Tally Architecture**
- **Individual Tally Databases**: Each tally relationship has its own SQL database
- **Shared Database Instance**: Partners synchronize via P2P protocols  
- **Local Tally Registry**: Master list of all user's tally relationships
- **Partner Discovery**: Via Kademlia DHT and libp2p network protocols

### **Core Tables Per Tally DB**
- `tally_config` - Relationship terms, credit limits, status
- `tally_transactions` - All transactions between partners
- `tally_invitations` - Invitation history and responses
- `tally_negotiations` - Credit limit change proposals
- `tally_disputes` - Conflict resolution records

### **Local Registry Tables**
- `my_tallies` - List of all tally relationships  
- `tally_templates` - Saved relationship templates
- `partner_cache` - Cached partner profile information

---

## 📱 API Procedures

### **tally.getAll()**
**Purpose**: Get list of all user's tally relationships  
**Database**: Query local `my_tallies` registry  
**Usage**: Tally list screens, relationship overview

**Parameters**:
```javascript
{
  status?: "all" | "active" | "pending" | "suspended",
  sortBy?: "name" | "balance" | "activity" | "created"
}
```

**Returns**:
```javascript
{
  tallies: [
    {
      id: string,          // Tally relationship ID
      partnerId: string,   // Partner's user ID
      partnerName: string, // Partner's display name
      partnerAvatar: string, // Partner's profile image/initials
      status: "active" | "pending" | "invited" | "suspended",
      balance: number,     // Current balance (positive = they owe you)
      creditLimits: {
        given: number,     // Credit you've extended to them
        received: number   // Credit they've extended to you
      },
      lastActivity: timestamp,
      created: timestamp,
      templateId?: string  // If created from template
    }
  ],
  summary: {
    total: number,         // Total number of tallies
    active: number,        // Active tallies
    pending: number        // Pending invitations
  }
}
```

**Screen Usage**:
- Tally list screen (tab root)
- Home dashboard tally summary
- Partner selection flows

---

### **tally.create(options)**
**Purpose**: Create new tally relationship with a partner  
**Database**: Create new tally database, update local registry  
**P2P**: Send invitation via libp2p network

**Parameters**:
```javascript
{
  partnerId: string,       // Partner's user ID
  myCreditLimit: number,   // Credit limit I'm setting for them
  requestedCreditLimit: number, // Credit limit I'm requesting from them
  templateId?: string,     // Optional template to use
  terms?: {
    description: string,   // Relationship description
    category: "personal" | "business" | "vendor",
    autoAcceptLimit?: number, // Auto-accept transactions under this amount
    expiryDate?: timestamp   // Optional relationship expiry
  },
  invitationMethod: "qr" | "email" | "link" | "direct"
}
```

**Returns**:
```javascript
{
  success: boolean,
  tallyId: string,         // Created tally ID
  invitationUrl: string,   // Shareable invitation URL
  qrCode?: string,         // Base64 QR code image (if requested)
  status: "pending",       // Initial status
  expiresAt: timestamp,    // Invitation expiry time
  errors?: string[]
}
```

**Screen Usage**:
- `tally-review.xml` → Complete tally creation flow
- Partner search and selection
- Template-based tally creation

---

### **tally.searchPartners(query)**
**Purpose**: Search for potential tally partners on the network  
**Database**: Query distributed P2P network via Kademlia DHT  
**Usage**: Partner discovery during tally creation

**Parameters**:
```javascript
{
  query: string,           // Name, email, or user ID
  filters?: {
    excludeExisting: boolean, // Exclude users with existing tallies
    category?: "personal" | "business" | "vendor",
    location?: {          // Geographic filtering
      latitude: number,
      longitude: number,
      radius: number      // In kilometers
    }
  },
  limit?: number          // Max results (default: 20)
}
```

**Returns**:
```javascript
{
  partners: [
    {
      id: string,         // User ID
      name: string,       // Display name
      avatar: string,     // Profile image or initials
      publicKey: string,  // Public key for verification
      category: string,   // "individual" | "business" | "vendor"
      verified: boolean,  // Identity verification status
      reputation?: {
        score: number,    // 0.0 to 5.0 reputation score
        tallyCount: number, // Number of active tallies
        references: number  // Number of positive references
      },
      distance?: number,  // Distance in km (if location provided)
      mutualConnections: number // Shared tally partners
    }
  ],
  hasMore: boolean,
  searchId: string        // For pagination
}
```

---

### **tally.getTemplates()**
**Purpose**: Get saved tally relationship templates  
**Database**: Query local `tally_templates` table  
**Usage**: Template selection during tally creation

**Parameters**: None

**Returns**:
```javascript
{
  templates: [
    {
      id: string,         // Template ID
      name: string,       // Template name
      description: string, // Template description
      category: "personal" | "business" | "vendor",
      defaultCreditLimit: number,
      terms: {
        autoAcceptLimit: number,
        description: string,
        expiryDuration?: number // Days until expiry
      },
      usageCount: number, // How many times used
      lastUsed?: timestamp
    }
  ]
}
```

**Screen Usage**:
- `tally-templates.xml` → Template management
- Template selection during tally creation
- Quick tally setup flows

---

### **tally.createTemplate(template)**
**Purpose**: Save a new tally relationship template  
**Database**: Insert into local `tally_templates` table

**Parameters**:
```javascript
{
  name: string,
  description: string,
  category: "personal" | "business" | "vendor",
  defaultCreditLimit: number,
  terms: {
    autoAcceptLimit?: number,
    description: string,
    expiryDuration?: number
  }
}
```

**Returns**:
```javascript
{
  success: boolean,
  templateId: string,
  template: TallyTemplate
}
```

---

### **tally.processInvitation(invitationData)**
**Purpose**: Process received tally invitation  
**Database**: Create tally database, send response via P2P  
**Usage**: Responding to email/QR invitations

**Parameters**:
```javascript
{
  invitationId: string,    // Invitation identifier
  action: "accept" | "reject" | "negotiate",
  counterOffer?: {
    myCreditLimit: number, // Credit limit I'm offering
    requestedCreditLimit: number, // Credit limit I want
    terms?: object
  },
  message?: string         // Optional message to sender
}
```

**Returns**:
```javascript
{
  success: boolean,
  tallyId?: string,        // Created tally ID (if accepted)
  status: "accepted" | "rejected" | "negotiating",
  nextStep?: string,       // Guidance for next action
  errors?: string[]
}
```

---

### **tally.updateCreditLimits(tallyId, limits)**
**Purpose**: Propose changes to credit limits  
**Database**: Update tally database, send proposal via P2P

**Parameters**:
```javascript
{
  tallyId: string,
  newLimits: {
    myCreditLimit: number,    // New credit I'm extending
    requestedCreditLimit: number // New credit I'm requesting
  },
  reason?: string            // Optional explanation
}
```

**Returns**:
```javascript
{
  success: boolean,
  proposalId: string,       // Negotiation proposal ID
  status: "pending",        // Awaiting partner response
  effectiveDate?: timestamp, // When changes take effect
  errors?: string[]
}
```

---

### **tally.getInvitations()**
**Purpose**: Get pending tally invitations (sent and received)  
**Database**: Query local invitation tracking and P2P network

**Parameters**:
```javascript
{
  type?: "sent" | "received" | "all",
  status?: "pending" | "expired" | "all"
}
```

**Returns**:
```javascript
{
  sent: [
    {
      id: string,
      partnerId: string,
      partnerName: string,
      creditLimits: object,
      sentAt: timestamp,
      expiresAt: timestamp,
      status: "pending" | "accepted" | "rejected" | "expired"
    }
  ],
  received: [
    {
      id: string,
      fromUserId: string,
      fromUserName: string,
      proposedCreditLimits: object,
      terms: object,
      receivedAt: timestamp,
      expiresAt: timestamp,
      message?: string
    }
  ]
}
```

---

### **tally.generateQRInvitation(tallyOptions)**
**Purpose**: Generate QR code for tally invitation sharing  
**Database**: Create invitation record, generate shareable URL

**Parameters**:
```javascript
{
  myCreditLimit: number,
  requestedCreditLimit: number,
  templateId?: string,
  expiryHours?: number,    // Hours until invitation expires
  message?: string         // Optional invitation message
}
```

**Returns**:
```javascript
{
  invitationId: string,
  url: string,             // Deep link URL for invitation
  qrCode: string,          // Base64 encoded QR code image
  expiresAt: timestamp,
  sharingText: string      // Pre-formatted sharing message
}
```

**Screen Usage**:
- `qr-share.xml` → QR code display and sharing
- Invitation sharing flows
- Link generation for email/SMS

---

## 🔄 P2P Network Integration

### **Partner Discovery**
- **Kademlia DHT**: Distributed partner search across network
- **Profile Caching**: Local cache of frequently searched partners  
- **Reputation System**: Network-based partner reputation scoring

### **Invitation Delivery**
- **Direct P2P**: Real-time invitation via libp2p connection
- **Fallback Methods**: Email, SMS, QR codes for offline partners
- **Invitation Tracking**: Status updates via P2P network

### **Conflict Resolution**
- **Optimystic**: Automatic conflict resolution for credit limit changes
- **Consensus**: Partner agreement required for major changes
- **Dispute Handling**: Escalation to network mediators if needed

---

## 🧪 Mock Implementation Examples

### **New User Scenario**
```javascript
const newUserTallies = {
  tallies: [],
  summary: { total: 0, active: 0, pending: 0 }
};

const newUserTemplates = {
  templates: [
    {
      id: "friend-template",
      name: "Friend/Family",
      category: "personal", 
      defaultCreditLimit: 100,
      terms: { autoAcceptLimit: 10 }
    }
  ]
};
```

### **Active User Scenario**
```javascript
const activeUserTallies = {
  tallies: [
    {
      id: "tally-sarah-001",
      partnerId: "user-sarah-123",
      partnerName: "Sarah Miller",
      partnerAvatar: "SM",
      status: "active",
      balance: 25.00,
      creditLimits: { given: 100, received: 200 },
      lastActivity: "2024-01-15T10:30:00Z"
    }
  ],
  summary: { total: 1, active: 1, pending: 0 }
};
```

---

*These tally procedures enable comprehensive partner relationship management in the distributed MyCHIPs network.*
