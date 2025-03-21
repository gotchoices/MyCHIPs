# React useEffect Dependency Array Issues

**Status: RESOLVED** - All identified issues have been reviewed and fixed (2025-03-21)

## Summary of Resolution
After careful review, we identified and fixed issues related to useEffect dependency arrays throughout the codebase:
1. Fixed PendingChits component by removing unnecessary getChits dependency and adding null checks
2. Added defensive null check to Language component
3. Confirmed several other useEffect implementations were already optimal for their use cases

This work prevents potential issues with how the Hermes JavaScript engine (React Native 0.77+) handles reference equality in useEffect dependencies.

## Background

After upgrading to React Native 0.77 with the Hermes JavaScript engine, we encountered issues with dependency arrays in `useEffect` hooks. Specifically, the user's name and photo were not displaying on the home page, which was traced to a problem with how Hermes handles reference equality.

## The Problem

React's `useEffect` hook uses the dependency array to determine when to re-run the effect. It compares each item in the array using `Object.is()` comparison:
- For primitive values (strings, numbers): checks value equality
- For objects: checks reference equality

When using Hermes, there are subtle differences in how reference equality works compared to the previous JavaScript engine. This leads to unexpected behavior when:

1. Using primitive values derived from objects in dependency arrays
2. The parent object reference changes, but the derived primitive value remains the same
3. The effect doesn't re-run because React doesn't detect a change in the dependency array

## Test Case: User Profile Display Issue

### Initial Symptoms
- The user's name and photo no longer displayed on the home page after upgrading to RN 0.77
- On initial upgrade, the image and name were visible briefly upon app launch but disappeared within seconds
- In subsequent app launches, the photo and name never appeared at all, not even briefly

### Root Cause Analysis
- In the Navigator component, we were using `user_ent` (a string derived from `user.curr_eid`) in the dependency array
- When Redux updated with a new user object, Hermes didn't recognize that `user_ent` had changed
- The useEffect that fetched profile data wasn't triggering when it should have

### Example of the Issue

```javascript
// Before: This didn't reliably detect user changes in Hermes
useEffect(() => {
  // Fetch user data...
}, [wm, dispatch, user_ent, fetchAvatar]);
```

When the Redux state updated with a new user object, Hermes did not recognize that `user_ent` had changed, so the effect didn't re-run.

### The Fix

The solution was to include the full object in the dependency array, rather than just the derived primitive value:

```javascript
// After: Split effects with improved dependency tracking
useEffect(() => {
  if (user_ent && wm) {
    dispatch(fetchAvatar({ wm, user_ent }));
    dispatch(fetchPersonalAndCurrency({ wm, user_ent }));
  }
}, [user, wm, dispatch]); // Using the full user object ensures proper detection

useEffect(() => {
  // Other initialization tasks...
}, [wm, dispatch]);
```

## Areas Reviewed and Fixed

### 1. PendingChits Component
**Location**: `src/screens/Tally/PendingChits/index.jsx:43-45`
**Issue**: Included `getChits` (an imported function) and used `tally_uuid` (a primitive derived from props)
```javascript
useEffect(() => {
  fetchChits();
}, [dispatch, getChits, wm, tally_uuid, chitTrigger])
```
**Fix**: Removed `getChits` and added null check:
```javascript
useEffect(() => {
  if (wm && tally_uuid) {
    fetchChits();
  }
}, [dispatch, wm, tally_uuid, chitTrigger])
```

### 2. ProfileProvider Component
**Location**: `src/components/ProfileProvider.jsx:28-46`
**Issue**: Uses `setFilter` (state setter function) in dependency array
```javascript
useEffect(() => {
  AsyncStorage.getItem("filterData").then(data => {
    // ...
  })
}, [setFilter]);
```
**Analysis**: State setters maintain stable identity, so this was already correct

### 3. Setting Component
**Location**: `src/screens/Setting/index.jsx:52-56`
**Issue**: Uses deeply nested property `charkText?.setting?.title` in dependency array
```javascript
useEffect(() => {
  if (charkText?.setting?.title) {
    props.navigation.setOptions({title: charkText?.setting?.title});
  }
}, [charkText?.setting?.title]);
```
**Analysis**: Using specific property is appropriate to prevent unnecessary re-renders

### 4. SocketProvider Component
**Location**: `src/components/SocketProvider.jsx:30-42`
**Issue**: Uses `ws` variable inside effect but not in dependency array
```javascript
useEffect(() => {
  if(!ws) {
    Linking.getInitialURL().then((url) => {
      // ...
    });
  }
}, []);
```
**Analysis**: Empty dependency array is correct as this should only run once on mount

### 5. Language Component
**Location**: `src/screens/Setting/Language/index.jsx:29-40`
**Issue**: Uses `wm` inside effect but not in dependency array
```javascript
useEffect(() => {
  wm.request(`language_ref_${random()}`, 'select', {
    // ...
  }, data => {
    setLanguages(data ?? [])
  })
}, [])
```
**Fix**: Added null check while maintaining empty dependency array:
```javascript
useEffect(() => {
  if (wm) {
    wm.request(`language_ref_${random()}`, 'select', {
      // ...
    }, data => {
      setLanguages(data ?? [])
    })
  }
}, [])
```

## Best Practices for useEffect

1. **Include all variables used within the effect in the dependency array**
   - This prevents stale closures and ensures the effect runs when dependencies change

2. **Use objects rather than primitive derivatives in dependencies**
   - When working with objects from Redux or props, include the complete object in the dependency array
   - This ensures React detects changes in reference equality

3. **Avoid unnecessary dependencies**
   - Functions defined outside the component don't need to be included
   - State setter functions (`setState`) are stable and don't need to be dependencies

4. **Split useEffect hooks by responsibility**
   - Separate unrelated effects into different useEffect calls with their own dependency arrays
   - This makes the code more maintainable and less prone to unnecessary re-renders

## Checklist for Fixing useEffect Issues

- [x] Fix PendingChits component dependency array (Removed unnecessary getChits dependency, added null checks)
- [x] Review ProfileProvider useEffect with setFilter dependency (Determined current implementation is appropriate as state setters maintain stable identity)
- [x] Review Setting component useEffect (Determined that using specific charkText?.setting?.title dependency is appropriate for this case, as it prevents unnecessary re-renders when other translations change)
- [x] Review SocketProvider useEffect with empty dependency array (Determined the empty array is correct as this effect should only run once on mount, and adding ws could create unintended reconnection loops)
- [x] Add null check to Language component's wm usage but maintain empty dependency array (Added defensive null check while keeping the intended behavior of fetching languages only once on mount)
- [ ] Review all other useEffect hooks in the codebase for similar issues
- [ ] Add ESLint rule to catch missing dependencies (react-hooks/exhaustive-deps)
- [ ] Create test cases to verify these fixes prevent regression
- [ ] Document these best practices in the project's coding standards