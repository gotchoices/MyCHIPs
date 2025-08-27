# Balance & Account Summary API

*Balance calculations, account summaries, and financial overview procedures*

## 🏗️ Database Context

### **Multi-Database Architecture**
- **Local Database**: User's personal financial cache and preferences
- **Tally Databases**: Individual databases for each tally relationship
- **Aggregation Logic**: Engine combines data across all tally DBs to calculate totals

### **Key Tables Per Tally DB**
- `tally_transactions` - Individual transaction records
- `tally_balances` - Current balance state between partners
- `tally_limits` - Credit limits and terms
- `tally_metadata` - Relationship details and status

### **Local Cache Tables**
- `balance_cache` - Cached aggregated balance (for performance)
- `balance_history` - Historical balance snapshots
- `account_summary` - Pre-calculated summary statistics

---

## 📱 API Procedures

### **balance.getSummary()**
**Purpose**: Get current aggregated balance across all tallies  
**Database**: Aggregate across all tally databases, cache locally  
**Usage**: Home dashboard, balance displays, quick balance checks

**Parameters**: None

**Returns**:
```javascript
{
  total: number,        // Total balance across all tallies (in CHIPs)
  currency: "CHIP",     // Primary currency unit
  formatted: string,    // Formatted display string "¢1,247.50"
  description: string,  // Status description
  lastUpdated: timestamp,
  breakdown: {
    positive: number,   // Total positive balances (others owe you)
    negative: number,   // Total negative balances (you owe others)
    activeTallies: number, // Number of tallies with non-zero balance
    totalTallies: number   // Total number of tally relationships
  }
}
```

**Screen Usage**:
- `home-dashboard.xml` → `<balance-summary data-total="¢1,247.50"/>`
- Balance card components throughout app
- Quick balance checks in navigation

**Example Response**:
```javascript
{
  total: 1247.50,
  currency: "CHIP", 
  formatted: "¢1,247.50",
  description: "Available to spend",
  lastUpdated: "2024-01-15T10:30:00Z",
  breakdown: {
    positive: 1500.00,  // Sarah owes you $1500
    negative: -252.50,  // You owe Coffee Shop $252.50
    activeTallies: 3,
    totalTallies: 5
  }
}
```

---

### **balance.getDetailed()**
**Purpose**: Get detailed balance breakdown by tally partner  
**Database**: Query all tally databases for current balances  
**Usage**: Detailed balance view, tally management screens

**Parameters**:
```javascript
{
  includeZeroBalances?: boolean, // Include tallies with zero balance
  sortBy?: "balance" | "name" | "activity" // Sort order
}
```

**Returns**:
```javascript
{
  totalBalance: number,
  tallies: [
    {
      tallyId: string,     // Tally relationship ID
      partnerId: string,   // Partner user ID
      partnerName: string, // Partner display name
      balance: number,     // Current balance (positive = they owe you)
      creditLimit: {
        given: number,     // Credit you've extended to them
        received: number   // Credit they've extended to you
      },
      lastActivity: timestamp,
      status: "active" | "pending" | "suspended"
    }
  ]
}
```

---

### **balance.getHistory(options)**
**Purpose**: Get historical balance data for charts and trends  
**Database**: Query local `balance_history` table and tally transaction logs

**Parameters**:
```javascript
{
  period: "day" | "week" | "month" | "year",
  limit?: number,       // Number of data points
  tallyId?: string     // Specific tally (optional)
}
```

**Returns**:
```javascript
{
  dataPoints: [
    {
      timestamp: string,
      balance: number,
      change: number,    // Change since previous point
      transactions: number // Number of transactions in period
    }
  ],
  summary: {
    startBalance: number,
    endBalance: number,
    totalChange: number,
    trend: "increasing" | "decreasing" | "stable"
  }
}
```

---

### **balance.subscribe(callback)**
**Purpose**: Subscribe to real-time balance updates  
**Database**: Listen for changes across all tally databases  
**Usage**: Live balance updates in UI

**Parameters**:
```javascript
callback: (balanceUpdate: BalanceSummary) => void
```

**Returns**:
```javascript
{
  unsubscribe: () => void  // Function to stop listening
}
```

**Usage Example**:
```javascript
const { unsubscribe } = await balance.subscribe((newBalance) => {
  setBalance(newBalance);
  // Show notification for significant changes
  if (Math.abs(newBalance.total - currentBalance) > 10) {
    showBalanceChangeNotification(newBalance);
  }
});

// Cleanup on component unmount
return unsubscribe;
```

---

### **balance.getCreditLimits()**
**Purpose**: Get overview of credit limits across all tallies  
**Database**: Aggregate credit limit data from all tally databases

**Parameters**: None

**Returns**:
```javascript
{
  totalCreditGiven: number,    // Total credit extended to others
  totalCreditReceived: number, // Total credit available from others
  utilizationRate: number,     // 0.0 to 1.0, how much credit is used
  creditBreakdown: [
    {
      tallyId: string,
      partnerName: string,
      creditGiven: number,     // Credit limit you've set for them
      creditUsed: number,      // How much they've used
      creditReceived: number,  // Credit limit they've set for you  
      creditAvailable: number  // How much you can still spend
    }
  ]
}
```

---

### **balance.refreshCache()**
**Purpose**: Force refresh of cached balance data  
**Database**: Recalculate balances from all tally databases, update cache  
**Usage**: Pull-to-refresh, manual sync operations

**Parameters**:
```javascript
{
  forceFull?: boolean  // Force full recalculation vs. incremental
}
```

**Returns**:
```javascript
{
  success: boolean,
  balanceSummary: BalanceSummary,
  syncedTallies: number,
  errors?: string[]     // Any sync errors encountered
}
```

---

## 🔄 Real-Time Updates & Synchronization

### **Update Triggers**
Balance updates occur when:
- New transactions are received via P2P network
- Tally credit limits are modified
- New tally relationships are established
- Conflict resolution completes for disputed transactions

### **Optimistic Updates**
For responsive UI:
1. **Immediate UI update** when user initiates transaction
2. **Optimistic balance calculation** based on pending transaction
3. **Confirmation or rollback** when P2P network confirms/rejects

### **Conflict Resolution**
When tally partners have conflicting balance data:
1. **Temporary inconsistent state** shown with warning indicator
2. **Automatic resolution** via optimystic conflict resolution
3. **Updated balance** once consensus reached

---

## 📊 Performance Considerations

### **Caching Strategy**
- **Local cache** updated immediately for UI responsiveness
- **Background sync** with tally databases every 30 seconds
- **Full recalculation** only when cache invalidated

### **Large Tally Networks**
For users with many tally relationships:
- **Pagination** of detailed tally breakdowns
- **Lazy loading** of historical data
- **Priority sync** for most active tallies first

---

## 🧪 Mock Implementation Examples

### **New User (No Tallies)**
```javascript
const newUserBalance = {
  total: 0,
  currency: "CHIP",
  formatted: "¢0.00", 
  description: "No active tallies",
  breakdown: {
    positive: 0,
    negative: 0,
    activeTallies: 0,
    totalTallies: 0
  }
};
```

### **Active User (Multiple Tallies)**
```javascript
const activeUserBalance = {
  total: 1247.50,
  currency: "CHIP",
  formatted: "¢1,247.50",
  description: "Available to spend",
  breakdown: {
    positive: 1500.00,  // Sarah owes $1500
    negative: -252.50,  // Owes Coffee Shop $252.50  
    activeTallies: 3,
    totalTallies: 5
  }
};
```

### **Business User (High Volume)**
```javascript
const businessUserBalance = {
  total: 15420.75,
  currency: "CHIP", 
  formatted: "¢15,420.75",
  description: "Strong positive balance",
  breakdown: {
    positive: 18500.00,
    negative: -3079.25,
    activeTallies: 45,
    totalTallies: 67
  }
};
```

---

*These balance procedures provide comprehensive financial overview capabilities for the distributed MyCHIPs system.*
