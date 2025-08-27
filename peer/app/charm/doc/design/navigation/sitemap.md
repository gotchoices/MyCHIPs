# Navigation Sitemap

*Complete navigation tree for the MyCHIPs mobile app*

## 🗂️ Primary Navigation Structure

### 🏠 **HOME** Tab
*Dashboard, balance overview, getting started guidance*

```
HOME
├── Dashboard (home-dashboard.xml) ← Tab Root
├── Transaction Detail (modal)
├── Balance History (push)
└── Quick Actions
    ├── Send Payment (modal)
    ├── Request Payment (modal)
    └── Share QR (qr-share.xml)
```

**Tab State**: Home icon active (#007AFF)  
**Breadcrumbs**: None (tab root)

---

### 📄 **INVOICE** Tab  
*Send and receive payment requests, invoice management*

```
INVOICE
├── Invoice List ← Tab Root
├── Create Invoice (modal)
├── Invoice Detail (push)
│   ├── Edit Invoice (modal)
│   └── Share Invoice (modal)
├── Payment Requests (push)
│   └── Request Detail (push)
└── Templates (push)
    ├── Create Template (modal)
    └── Edit Template (modal)
```

**Tab State**: Invoice icon active (#007AFF)  
**Breadcrumbs**: "Invoice > [Context]" for sub-screens

---

### 📷 **SCAN** Tab
*QR code scanner for payments and tally invitations*

```
SCAN
├── QR Scanner ← Tab Root
├── Manual Entry (modal)
├── Payment Confirmation (modal)
├── Tally Invitation (modal)
└── Scan History (push)
    └── Scan Detail (push)
```

**Tab State**: Scan icon active (#007AFF)  
**Breadcrumbs**: "Scan > [Context]" for sub-screens

---

### 🤝 **TALLY** Tab
*Tally relationships, partner management, credit limits*

```
TALLY
├── Tally List ← Tab Root
├── Partner Profile (push)
│   ├── Edit Credit Limit (modal)
│   ├── Transaction History (push)
│   └── Tally Settings (push)
├── Create Tally (tally-review.xml)
│   ├── Partner Search (modal)
│   ├── Template Selection (tally-templates.xml)
│   ├── Credit Negotiation (modal)
│   └── Share Invitation (qr-share.xml)
├── Pending Invitations (push)
│   ├── Review Invitation (modal)
│   └── Respond to Invitation (modal)
└── Marketplace Partners (marketplace.xml)
    └── Vendor Profile (push)
```

**Tab State**: Tally icon active (#007AFF)  
**Breadcrumbs**: "Tally > [Context] > [Sub-context]" for deep navigation

---

### ⚙️ **SETTINGS** Tab
*Account management, security, preferences*

```
SETTINGS
├── Settings Home ← Tab Root
├── Account (push)
│   ├── Edit Profile (identity-setup.xml)
│   ├── Backup & Recovery (push)
│   └── Export Data (modal)
├── Security (push)
│   ├── Change PIN (modal)
│   ├── Biometric Settings (push)
│   └── Device Management (push)
├── Preferences (push)
│   ├── Notifications (push)
│   ├── Currency Display (push)
│   └── Language (push)
├── Support (push)
│   ├── Help Articles (push)
│   ├── Contact Support (modal)
│   └── Report Issue (modal)
└── About (push)
    ├── Terms of Service (modal)
    ├── Privacy Policy (modal)
    └── Licenses (push)
```

**Tab State**: Settings icon active (#007AFF)  
**Breadcrumbs**: "Settings > [Category] > [Sub-category]" for nested navigation

---

## 🚀 Onboarding Flow
*First-time user experience (outside main navigation)*

```
ONBOARDING
├── App Launch (app-launch.xml) ← Entry Point
├── Identity Setup (identity-setup.xml)
├── First Tally Invitation (modal)
├── Getting Started Tutorial (modal)
└── → Redirect to HOME tab
```

**Navigation**: Modal over entire app, no tab bar visible  
**Exit**: Onboarding completion leads to Home tab

---

## 🔗 Cross-Tab Navigation Patterns

### Deep Links
- **Payment URLs**: `mychips://pay/[id]` → Scan tab
- **Tally Invitations**: `mychips://tally/[id]` → Tally tab  
- **Invoice Links**: `mychips://invoice/[id]` → Invoice tab
- **Settings Deep Links**: `mychips://settings/account` → Settings tab

### Modal Presentations (App-Level)
- **QR Share** (`qr-share.xml`) - Can be triggered from any tab
- **Payment Confirmation** - Triggered from Scan or Invoice
- **Tally Creation** (`tally-review.xml`) - Can be triggered from Home or Tally

### Universal Actions
- **Emergency Contact** - Accessible from any screen via gesture
- **Network Status** - Global banner when offline
- **Notifications** - Toast messages over current screen

---

## 📱 Screen Transition Types

| Transition | Usage | Animation | Back Behavior |
|------------|-------|-----------|---------------|
| **Tab Switch** | Primary navigation | Cross-fade | Return to previous tab |
| **Push** | Navigate deeper in tab | Slide from right | Pop to previous screen |
| **Modal** | Complex forms, actions | Slide up from bottom | Dismiss to previous state |
| **Overlay** | Temporary info, alerts | Fade in | Tap outside to dismiss |

---

## 🎯 Current Implementation Status

### ✅ Completed Screens
- **home-dashboard.xml** → HOME tab root
- **marketplace.xml** → TALLY tab > Marketplace Partners  
- **tally-review.xml** → TALLY tab > Create Tally
- **qr-share.xml** → Universal modal (accessible from multiple tabs)
- **tally-templates.xml** → TALLY tab > Create Tally > Template Selection
- **app-launch.xml** → Onboarding entry
- **identity-setup.xml** → Onboarding + Settings

### 🚧 Screens Needed
- **Invoice List** (INVOICE tab root)
- **QR Scanner** (SCAN tab root)  
- **Tally List** (TALLY tab root)
- **Settings Home** (SETTINGS tab root)
- Plus ~20 additional screens for complete navigation tree

### 🔄 Screens Requiring Updates
Most existing screens need tab bar updates to match new 5-tab structure (Home, Invoice, Scan, Tally, Settings)

---

*This sitemap serves as the master reference for all navigation decisions. Update this document whenever adding or modifying screens.*
