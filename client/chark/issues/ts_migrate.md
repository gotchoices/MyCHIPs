# TypeScript Migration Checklist

## Initial Setup
[ ] Install TypeScript and dependencies:
    ```sh
    npm install --save-dev typescript @types/react @types/react-native @types/jest
    ```

[ ] Create tsconfig.json in project root:
    ```json
    {
      "extends": "@react-native/typescript-config/tsconfig.json",
      "compilerOptions": {
        "strict": true,
        "allowJs": true,
        "skipLibCheck": true
      },
      "include": ["src/\*/\*", "index.js"]
    }
    ```

[ ] Update metro.config.js to handle TypeScript:
    ```js
    resolver: {
      sourceExts: ['js', 'jsx', 'json', 'ts', 'tsx', 'svg'],
    }
    ```

## Project Structure
[ ] Create types directory:
    ```sh
    mkdir src/types
    ```

[ ] Create base type definitions:
    - [ ] src/types/navigation.ts (for navigation types)
    - [ ] src/types/redux.ts (for Redux state types)
    - [ ] src/types/api.ts (for API response types)
    - [ ] src/types/components.ts (for shared component props)

## Component Migration
[ ] Convert core components:
    - [ ] App.js → App.tsx
    - [ ] src/components/SocketProvider.jsx → SocketProvider.tsx
    - [ ] src/components/MessageTextProvider.jsx → MessageTextProvider.tsx
    - [ ] src/components/Toast.jsx → Toast.tsx
    - [ ] src/components/Spinner/index.jsx → Spinner/index.tsx

[ ] Convert screens:
    - [ ] src/screens/Tally/\*/\*.jsx → .tsx
    - [ ] src/screens/Profile/\*/\*.jsx → .tsx
    - [ ] src/screens/Settings/\*/\*.jsx → .tsx

## Utility Functions
[ ] Convert utility files:
    - [ ] src/utils/language.js → language.ts
    - [ ] src/utils/message-signature.js → message-signature.ts
    - [ ] src/utils/common.js → common.ts
    - [ ] src/utils/notification.js → notification.ts

## Redux Integration
[ ] Add TypeScript to Redux:
    - [ ] src/redux/store.js → store.ts
    - [ ] Add types for actions and reducers
    - [ ] Update useSelector and useDispatch hooks with proper types

## API and Services
[ ] Convert API-related files:
    - [ ] src/services/\*\*/\*.js → .ts
    - [ ] Add type definitions for API responses
    - [ ] Add error handling types

## Testing
[ ] Update test files:
    - [ ] Convert test files to TypeScript
    - [ ] Add type definitions for test utilities
    - [ ] Update Jest configuration for TypeScript

## Final Steps
[ ] Run type checking:
    ```sh
    npx tsc --noEmit
    ```

[ ] Update ESLint configuration:
    ```sh
    npm install --save-dev @typescript-eslint/parser @typescript-eslint/eslint-plugin
    ```

[ ] Update .eslintrc.js to include TypeScript rules

[ ] Clean up:
    - [ ] Remove PropTypes (replaced by TypeScript interfaces)
    - [ ] Remove JSDoc comments (replaced by TypeScript types)
    - [ ] Update documentation to reflect TypeScript usage

## Migration Progress Tracking
| Component/File | Status | Notes |
|---------------|--------|-------|
| App.tsx | [ ] | Core application file |
| SocketProvider.tsx | [ ] | WebSocket connection management |
| MessageTextProvider.tsx | [ ] | Text message handling |
| Toast.tsx | [ ] | Notification component |
| Spinner/index.tsx | [ ] | Loading indicator |
| Tally screens | [ ] | Multiple files to convert |
| Profile screens | [ ] | Multiple files to convert |
| Settings screens | [ ] | Multiple files to convert |

## Notes
- Keep JavaScript files working alongside TypeScript during migration
- Convert one component at a time and test thoroughly
- Use `allowJs: true` in tsconfig.json to support gradual migration
- Add type definitions for third-party libraries as needed

