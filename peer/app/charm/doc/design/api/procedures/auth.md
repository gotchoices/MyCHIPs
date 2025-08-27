# Authentication & Identity Management API

*User identity, authentication, and profile management procedures*

## 🏗️ Database Context

### **Local Database Tables**
- `user_profile` - Core identity information (private)
- `user_keys` - Cryptographic keys and certificates (private)
- `onboarding_state` - Tutorial progress and setup status (private)
- `device_settings` - App preferences and configurations (private)

### **P2P Network Integration**
- Identity verification via distributed identity system
- Public key distribution for tally partner verification
- Profile discovery for partner search operations

---

## 📱 API Procedures

### **auth.getProfile()**
**Purpose**: Retrieve current user's profile information  
**Database**: Query local `user_profile` table  
**Usage**: App launch, identity setup, profile display

**Parameters**: None

**Returns**:
```javascript
{
  id: string,           // Unique user identifier (UUID)
  name: string,         // Display name
  email: string,        // Email address
  avatar?: string,      // Profile image URL or initials
  publicKey: string,    // Public key for tally operations
  created: timestamp,   // Account creation date
  verified: boolean     // Email/identity verification status
}
```

**Screen Usage**:
- `identity-setup.xml` → Pre-populate form fields
- `home-dashboard.xml` → Display user name in header
- Profile screens → Show complete user information

---

### **auth.updateProfile(data)**
**Purpose**: Update user profile information  
**Database**: Update local `user_profile` table  
**P2P**: Propagate public profile changes to network

**Parameters**:
```javascript
{
  name?: string,        // Updated display name
  email?: string,       // Updated email address
  avatar?: string,      // Updated profile image
}
```

**Returns**:
```javascript
{
  success: boolean,
  profile: UserProfile, // Updated profile object
  errors?: string[]     // Validation errors if any
}
```

**Validation Rules**:
- Name: 2-50 characters, alphanumeric + spaces
- Email: Valid email format, uniqueness check via P2P network
- Avatar: Image URL or 2-letter initials

---

### **auth.initializeIdentity(identityData)**
**Purpose**: Create new user identity during onboarding  
**Database**: Insert into `user_profile`, `user_keys` tables  
**P2P**: Register identity on distributed network

**Parameters**:
```javascript
{
  name: string,         // User's full name
  email: string,        // Email address
  avatar?: string,      // Optional profile image
  generateKeys: boolean // Whether to generate new key pair
}
```

**Returns**:
```javascript
{
  success: boolean,
  userId: string,       // Generated user ID
  publicKey: string,    // Generated public key
  backupPhrase: string, // Recovery seed phrase
  errors?: string[]
}
```

**Side Effects**:
- Generates cryptographic key pair
- Creates backup/recovery seed phrase
- Registers identity on P2P network
- Initializes onboarding state

---

### **auth.getOnboardingState()**
**Purpose**: Retrieve current onboarding progress  
**Database**: Query local `onboarding_state` table  
**Usage**: Determine which tutorial steps are complete

**Parameters**: None

**Returns**:
```javascript
{
  isComplete: boolean,
  currentStep: string,  // "identity" | "first-tally" | "marketplace" | "complete"
  tasks: [
    {
      id: string,       // "setup-identity", "create-tally", "find-vendors"
      title: string,    // "Set up your identity"
      description: string,
      completed: boolean,
      required: boolean
    }
  ],
  progress: number      // 0.0 to 1.0 completion percentage
}
```

**Screen Usage**:
- `app-launch.xml` → Determine if onboarding needed
- `home-dashboard.xml` → Show getting started tasks
- Navigation → Route to appropriate onboarding step

---

### **auth.completeOnboardingTask(taskId)**
**Purpose**: Mark an onboarding task as completed  
**Database**: Update local `onboarding_state` table

**Parameters**:
```javascript
{
  taskId: string,       // Task identifier to complete
  metadata?: object     // Optional task-specific data
}
```

**Returns**:
```javascript
{
  success: boolean,
  updatedState: OnboardingState,
  nextTask?: string     // Suggested next task ID
}
```

**Examples**:
```javascript
// Mark identity setup as complete
await auth.completeOnboardingTask("setup-identity");

// Mark first tally creation as complete
await auth.completeOnboardingTask("create-tally", { 
  tallyId: "tally-123",
  partnerId: "user-456" 
});
```

---

### **auth.searchUsers(query)**
**Purpose**: Search for potential tally partners by name/email  
**Database**: Query distributed P2P network for public profiles  
**Usage**: Partner discovery during tally creation

**Parameters**:
```javascript
{
  query: string,        // Name or email search term
  limit?: number,       // Max results (default: 10)
  excludeExisting?: boolean // Exclude users with existing tallies
}
```

**Returns**:
```javascript
{
  users: [
    {
      id: string,       // User ID
      name: string,     // Display name
      email: string,    // Email address (if public)
      avatar: string,   // Profile image or initials
      publicKey: string,// Public key for verification
      verified: boolean,// Identity verification status
      mutualConnections?: number // Shared tally partners
    }
  ],
  hasMore: boolean      // Whether more results available
}
```

**Privacy Considerations**:
- Only returns users who have made their profiles discoverable
- Email addresses may be masked for privacy
- Search results filtered by user's privacy settings

---

### **auth.verifyIdentity(userId, challenge)**
**Purpose**: Verify a user's identity for tally creation  
**Database**: Local verification cache, P2P identity verification  
**Usage**: Confirm partner identity before creating tally

**Parameters**:
```javascript
{
  userId: string,       // User to verify
  challenge?: string    // Optional verification challenge
}
```

**Returns**:
```javascript
{
  verified: boolean,
  confidence: number,   // 0.0 to 1.0 verification confidence
  verificationMethod: string, // "email" | "key" | "network"
  profile: UserProfile, // Verified profile information
  warnings?: string[]   // Any verification concerns
}
```

---

## 🔒 Security Considerations

### **Key Management**
- Private keys stored securely in device keychain/secure storage
- Public keys distributed via P2P network for partner verification
- Backup seed phrases generated for account recovery

### **Privacy Protection**
- User profiles can be configured as public or private
- Email addresses optionally masked in search results
- Location and activity data never included in public profiles

### **Identity Verification**
- Multi-factor verification via email, key signatures, network consensus
- Reputation systems to identify trusted vs. new identities
- Protection against Sybil attacks via network-based verification

---

## 🧪 Mock Implementation Examples

### **Development Scenarios**
```javascript
// New user scenario
const newUserProfile = {
  id: "user-new-001",
  name: "",
  email: "",
  verified: false,
  created: new Date(),
  onboardingState: {
    isComplete: false,
    currentStep: "identity",
    progress: 0.0
  }
};

// Active user scenario
const activeUserProfile = {
  id: "user-active-001", 
  name: "Alex Chen",
  email: "alex@example.com",
  avatar: "AC",
  verified: true,
  onboardingState: {
    isComplete: true,
    progress: 1.0
  }
};
```

---

*These authentication procedures provide the foundation for user identity management in the distributed MyCHIPs system.*
