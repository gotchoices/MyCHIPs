# Mock API Implementation

*Mock data and procedures for development and testing of the MyCHIPs mobile app*

## 🎯 Purpose

The mock API layer enables:
- **UI Development** without waiting for the distributed engine
- **User Story Testing** with realistic data scenarios
- **Integration Testing** with predictable responses
- **Error Simulation** for edge case handling

## 📁 Structure

```
mock/
├── README.md           # This file - mock strategy and usage
├── data/               # Static mock datasets
│   ├── users.json     # Sample user profiles
│   ├── tallies.json   # Sample tally relationships
│   ├── transactions.json # Sample transaction history
│   ├── vendors.json   # Sample marketplace vendors
│   └── templates.json # Sample tally templates
├── procedures.js       # Mock API implementations
└── scenarios/          # User story specific datasets
    ├── new-user.js    # Fresh install scenario
    ├── active-user.js # User with established tallies
    ├── business-user.js # High-volume business user
    └── error-cases.js # Error and edge case scenarios
```

## 🔄 Mock Implementation Strategy

### **Development Phases**

#### **Phase 1: Static Mocks** (Immediate)
```javascript
// Simple static responses for rapid UI development
const mockBalance = {
  async getSummary() {
    return {
      total: 1247.50,
      currency: "CHIP",
      formatted: "¢1,247.50",
      description: "Available to spend"
    };
  }
};
```

#### **Phase 2: Interactive Mocks** (User Flow Testing)  
```javascript
// State-preserving mocks for realistic user interactions
class InteractiveMockBalance {
  constructor() {
    this.currentBalance = 1247.50;
    this.subscribers = [];
  }
  
  async getSummary() {
    return { total: this.currentBalance, ... };
  }
  
  async processTransaction(amount) {
    this.currentBalance += amount;
    this.notifySubscribers();
  }
}
```

#### **Phase 3: Engine Integration** (Production)
```javascript
// Real engine integration with same API interface
const realBalance = {
  async getSummary() {
    return await engineCore.balance.getCurrentBalance();
  }
};
```

### **Scenario Management**

The mock system supports multiple user scenarios:

```javascript
// Switch scenarios via environment variables or runtime config
const mockApi = createMockApi({
  scenario: process.env.MOCK_SCENARIO || 'active-user'
});

// Available scenarios:
// - 'new-user': Fresh install, onboarding needed
// - 'active-user': Established user with tallies and transactions
// - 'business-user': High-volume merchant/business account
// - 'error-states': Network failures, validation errors
```

## 🧪 Scenario Descriptions

### **New User Scenario**
- **Profile**: Empty name/email, unverified
- **Onboarding**: 0% complete, identity setup needed
- **Tallies**: None
- **Balance**: ¢0.00
- **Marketplace**: Shows getting started guidance

**Usage**: Testing onboarding flows, first-time user experience

### **Active User Scenario**  
- **Profile**: Alex Chen, verified user
- **Onboarding**: 100% complete
- **Tallies**: 3 active relationships (Sarah, Coffee Shop, Local Market)
- **Balance**: ¢1,247.50 total
- **Transactions**: Recent payment history

**Usage**: Main app functionality, established user flows

### **Business User Scenario**
- **Profile**: Green Valley Market (business account)
- **Tallies**: 45+ customer relationships
- **Balance**: ¢15,420.75 (high positive balance)
- **Transactions**: High volume transaction history
- **Marketplace**: Vendor profile management

**Usage**: Business features, performance testing, high-volume scenarios

### **Error Cases Scenario**
- **Network**: Simulated connection failures
- **Validation**: Invalid input responses
- **Conflicts**: Tally negotiation disputes
- **System**: Database errors, sync failures

**Usage**: Error handling, edge case testing, resilience validation

## 📱 Usage in React Native

### **Mock API Integration**
```javascript
// api/client.js
import { createMockApi } from './mock/procedures';
import { createEngineApi } from './engine/client';

export const api = process.env.NODE_ENV === 'development' 
  ? createMockApi({ scenario: 'active-user' })
  : createEngineApi(engineInstance);
```

### **Component Usage**
```javascript
// components/BalanceCard.js
import { api } from '../api/client';

const BalanceCard = () => {
  const [balance, setBalance] = useState(null);
  
  useEffect(() => {
    // Same API call works with mocks or real engine
    api.balance.getSummary().then(setBalance);
  }, []);
  
  return (
    <View>
      <Text>{balance?.formatted || '¢0.00'}</Text>
    </View>
  );
};
```

### **Development Workflow**
```bash
# Start with new user scenario
MOCK_SCENARIO=new-user npm start

# Test with active user data  
MOCK_SCENARIO=active-user npm start

# Test error handling
MOCK_SCENARIO=error-cases npm start

# Use real engine (when available)
NODE_ENV=production npm start
```

## 🔍 Testing Strategy

### **Unit Tests**
```javascript
// tests/api/balance.test.js
import { createMockApi } from '../mock/procedures';

describe('Balance API', () => {
  const mockApi = createMockApi({ scenario: 'active-user' });
  
  it('should return formatted balance', async () => {
    const balance = await mockApi.balance.getSummary();
    expect(balance.formatted).toBe('¢1,247.50');
  });
});
```

### **Integration Tests**
```javascript
// tests/flows/onboarding.test.js
import { createMockApi } from '../mock/procedures';

describe('Onboarding Flow', () => {
  const mockApi = createMockApi({ scenario: 'new-user' });
  
  it('should complete identity setup', async () => {
    const result = await mockApi.auth.initializeIdentity({
      name: 'Test User',
      email: 'test@example.com'
    });
    expect(result.success).toBe(true);
    
    const state = await mockApi.auth.getOnboardingState();
    expect(state.currentStep).toBe('first-tally');
  });
});
```

### **Performance Tests**
```javascript
// tests/performance/large-dataset.test.js
import { createMockApi } from '../mock/procedures';

describe('Large Dataset Performance', () => {
  const mockApi = createMockApi({ scenario: 'business-user' });
  
  it('should handle 1000+ transactions efficiently', async () => {
    const start = Date.now();
    const transactions = await mockApi.transaction.getHistory({ limit: 1000 });
    const duration = Date.now() - start;
    
    expect(transactions.length).toBe(1000);
    expect(duration).toBeLessThan(100); // < 100ms
  });
});
```

## 🚨 Error Simulation

### **Network Errors**
```javascript
// Simulate connection failures
const networkErrorApi = createMockApi({ 
  scenario: 'error-cases',
  errorRate: 0.2  // 20% of calls fail
});
```

### **Validation Errors**
```javascript
// Test input validation
await mockApi.tally.create({
  partnerId: 'invalid-id',
  myCreditLimit: -100  // Invalid negative limit
});
// Returns: { success: false, errors: ['Invalid credit limit'] }
```

### **Conflict Resolution**
```javascript
// Simulate tally conflicts
const conflictApi = createMockApi({ 
  scenario: 'conflict-resolution',
  conflictType: 'credit-limit-dispute'
});
```

## 📊 Data Generation

### **Realistic Data**
All mock data is generated to be:
- **Realistic**: Based on actual user story scenarios
- **Consistent**: Relationships between data objects maintained
- **Varied**: Different data patterns for thorough testing
- **Scalable**: Configurable dataset sizes

### **Time-Based Data**
```javascript
// Generate transaction history with realistic timing
const transactions = generateTransactions({
  count: 50,
  timeRange: '30-days',
  pattern: 'weekly-shopping'  // Realistic shopping patterns
});
```

### **Geographic Data** 
```javascript
// Generate vendors with realistic geographic distribution
const vendors = generateVendors({
  center: { lat: 40.7128, lng: -74.0060 }, // NYC
  radius: 25, // 25km radius
  density: 'urban'
});
```

---

*This mock system enables comprehensive testing and development of the MyCHIPs mobile app while maintaining compatibility with the eventual distributed engine integration.*
