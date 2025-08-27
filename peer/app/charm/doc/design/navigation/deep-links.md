# Deep Links and URL Routing

*URL patterns and deep linking specifications for the MyCHIPs mobile app*

## 🔗 URL Scheme Structure

**Base Scheme**: `mychips://`

**Pattern**: `mychips://[tab]/[screen]/[id]?[params]`

## 📱 Tab-Based Routes

### Home Tab Routes
```
mychips://home                          → Home dashboard
mychips://home/transaction/[id]         → Transaction detail modal
mychips://home/balance-history          → Balance history screen
mychips://home/send                     → Send payment modal
mychips://home/request                  → Request payment modal
mychips://home/qr-share                 → QR share modal
```

### Invoice Tab Routes  
```
mychips://invoice                       → Invoice list
mychips://invoice/create                → Create invoice modal
mychips://invoice/[id]                  → Invoice detail
mychips://invoice/[id]/edit             → Edit invoice modal
mychips://invoice/[id]/share            → Share invoice modal
mychips://invoice/requests              → Payment requests list
mychips://invoice/requests/[id]         → Request detail
mychips://invoice/templates             → Template list
mychips://invoice/templates/create      → Create template modal
mychips://invoice/templates/[id]/edit   → Edit template modal
```

### Scan Tab Routes
```
mychips://scan                          → QR scanner
mychips://scan/manual                   → Manual entry modal
mychips://scan/confirm                  → Payment confirmation modal
mychips://scan/tally-invite             → Tally invitation modal
mychips://scan/history                  → Scan history
mychips://scan/history/[id]             → Scan detail
```

### Tally Tab Routes
```
mychips://tally                         → Tally list
mychips://tally/[id]                    → Partner profile
mychips://tally/[id]/credit             → Edit credit limit modal
mychips://tally/[id]/history            → Transaction history
mychips://tally/[id]/settings           → Tally settings
mychips://tally/create                  → Create tally flow
mychips://tally/create/search           → Partner search modal
mychips://tally/create/templates        → Template selection
mychips://tally/create/negotiate        → Credit negotiation modal
mychips://tally/create/share            → Share invitation
mychips://tally/invitations             → Pending invitations
mychips://tally/invitations/[id]        → Review invitation modal
mychips://tally/invitations/[id]/respond → Respond to invitation modal
mychips://tally/marketplace             → Marketplace partners
mychips://tally/marketplace/[id]        → Vendor profile
```

### Settings Tab Routes
```
mychips://settings                      → Settings home
mychips://settings/account              → Account settings
mychips://settings/account/profile      → Edit profile
mychips://settings/account/backup       → Backup & recovery
mychips://settings/account/export       → Export data modal
mychips://settings/security             → Security settings
mychips://settings/security/pin         → Change PIN modal
mychips://settings/security/biometric   → Biometric settings
mychips://settings/security/devices     → Device management
mychips://settings/preferences          → User preferences
mychips://settings/preferences/notifications → Notification settings
mychips://settings/preferences/currency → Currency display
mychips://settings/preferences/language → Language settings
mychips://settings/support              → Support options
mychips://settings/support/help         → Help articles
mychips://settings/support/contact      → Contact support modal
mychips://settings/support/report       → Report issue modal
mychips://settings/about                → About app
mychips://settings/about/terms          → Terms of service modal
mychips://settings/about/privacy        → Privacy policy modal
mychips://settings/about/licenses       → Open source licenses
```

## 🚀 Special Routes

### Onboarding Routes
```
mychips://onboard                       → App launch screen
mychips://onboard/identity              → Identity setup
mychips://onboard/tutorial              → Getting started tutorial
mychips://onboard/first-tally           → First tally invitation
```

### Universal Actions
```
mychips://qr-share?[params]             → QR share modal (from any context)
mychips://pay/[id]                      → Payment confirmation
mychips://tally-invite/[id]             → Tally invitation response
mychips://invoice-pay/[id]              → Invoice payment flow
```

## 📧 External Link Patterns

### Email Integration
```
https://app.mychips.org/pay/[id]        → Payment link → mychips://pay/[id]
https://app.mychips.org/tally/[id]      → Tally invitation → mychips://tally-invite/[id]
https://app.mychips.org/invoice/[id]    → Invoice link → mychips://invoice-pay/[id]
```

### QR Code Patterns
```
mychips://pay/[id]?amount=[value]       → Payment with amount
mychips://tally-invite/[id]?template=[template] → Tally invitation with template
mychips://contact/[id]                  → Add contact and create tally
```

## 🔧 URL Parameters

### Common Parameters
- **`amount`** - Payment amount in CHIPs
- **`currency`** - Currency code (default: CHIP)
- **`memo`** - Payment description/memo
- **`template`** - Tally template ID
- **`return_url`** - Deep link to return after completion
- **`ref`** - Reference/tracking identifier

### Example URLs
```
mychips://pay/abc123?amount=25.50&memo=Coffee
mychips://tally-invite/def456?template=friend&return_url=mychips://home
mychips://invoice/ghi789?currency=USD&amount=100.00
```

## 📱 Platform-Specific Handling

### iOS Universal Links
```
https://app.mychips.org/[path]          → mychips://[path]
```

### Android App Links  
```
https://app.mychips.org/[path]          → mychips://[path]
```

### Web Fallback
When app not installed, redirect to:
```
https://mychips.org/download?redirect=[encoded_url]
```

## 🎯 Navigation State Management

### Link Resolution Priority
1. **Direct Screen Match** - Exact route exists
2. **Tab + Modal** - Open tab and present modal
3. **Tab + Push Stack** - Navigate through push hierarchy  
4. **Fallback** - Default to appropriate tab root

### State Preservation
- **Tab State** - Preserve existing tab navigation stacks
- **Modal State** - Close existing modals before opening new ones
- **Form State** - Warn user about unsaved changes

### Error Handling
- **Invalid Route** - Redirect to home with error toast
- **Missing Permissions** - Redirect to appropriate settings
- **Network Error** - Cache link for retry when online

---

## 🔄 Implementation Guidelines

### Screen XML Integration
Each screen should specify its deep link pattern:
```xml
<!-- Add to screen XML as comment -->
<!-- Deep Link: mychips://tally/create -->
<!-- Breadcrumb: Tally > Create Tally -->
<app-screen width="375" height="812" xmlns="http://mychips.io/ui">
    ...
</app-screen>
```

### Component Data Attributes
Link-enabled components should include routing data:
```xml
<button-primary 
    data-label="View Details" 
    data-action="navigate"
    data-route="mychips://invoice/123"/>
```

---

*These deep link patterns ensure consistent URL structure and enable seamless navigation from external sources like emails and QR codes.*
