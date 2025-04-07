# Avatar Image Fetching and Display

## Problem Description

The application currently has issues with avatar images in various screens:

1. In the TallyGraphic component, if a partner's avatar image is not in the cache, the component falls back to displaying text (CUID) instead of attempting to fetch the image.

2. When viewing certificate details, if an image isn't available in the cache, it displays "Image not in cache" without attempting to fetch it from the backend.

3. In the OpenTallyView screen, avatars are displayed inconsistently - some tallies show avatars while others don't, suggesting issues with the image fetching or caching mechanism.

4. Currently, image fetching is only triggered at the screen level for collections of tallies (in Activity, Tally, and Invite screens), but not for individual certificate images when needed.

5. There's no mechanism to trigger a fetch for a specific missing image, leaving users with a sub-optimal experience.

## Solution Goals

1. Implement reactive image loading that fetches missing images when viewing certificate details or any components that require avatar images.
  
2. Only fetch images that aren't already in the cache to avoid redundant network requests.

3. Store fetched images in both Redux state and AsyncStorage for persistence.

4. Provide visual feedback during image loading (loading indicator).

5. Ensure images are properly displayed in all relevant components (TallyGraphic, OpenTallyView, certificate details, etc.).

6. (Optional) Add a manual refresh option for failed image loads.

## Implementation Strategy

1. Enhance `fetchImagesByDigest` in avatarSlice:
   - Add support for fetching a specific digest
   - Track loading and error states per digest
   - Implement proper caching and error handling

2. Create a new hook for reactive image fetching:
   - `useAvatarImage(digest)` - Returns image URI and loading state
   - Automatically triggers fetch if image is not in cache

3. Integrate image fetching in key components:
   - DefaultCertificate component should use the hook to fetch missing images
   - TallyGraphic should utilize the hook for better reactivity
   - OpenTallyView should properly trigger image fetching

4. Improve image caching strategy:
   - Review AsyncStorage implementation
   - Consider adding TTL (Time To Live) for cached images
   - Implement proper cache invalidation

## Checklist of Files to Modify

- [ ] **Redux Store:**
  - [ ] `/src/redux/avatarSlice.js` - Enhance `fetchImagesByDigest` thunk to support fetching specific digests, add loading states

- [ ] **Service Layer:**
  - [ ] `/src/services/tally.js` - Review `fetchTallyFile` and `getHolderImage` functions for possible improvements

- [ ] **New Hook:** 
  - [ ] `/src/hooks/useAvatarImage.js` - Create a new hook for reactive image fetching

- [ ] **Components:**
  - [ ] `/src/components/TallyGraphic/index.jsx` - Update to use the new hook and handle loading states
  - [ ] `/src/components/Avatar/index.jsx` - Add loading indicator and error handling

- [ ] **Certificate Screens:**
  - [ ] `/src/screens/Tally/TallyCertificate/DefaultCertificate.jsx` - Implement reactive image fetching
  - [ ] `/src/screens/Tally/TallyCertificate/index.jsx` - Review image fetching triggers

- [ ] **Tally List Screens:**
  - [ ] `/src/screens/Tally/OpenTallyView/index.jsx` - Fix inconsistent avatar display
  - [ ] `/src/screens/Tally/TallyPreview/index.jsx` - Ensure proper image fetching
  - [ ] `/src/screens/Tally/TallyEditView.jsx` - Update to support new image fetching mechanism
  - [ ] `/src/screens/Tally/TallyItem/index.jsx` - Review to ensure consistent image display
  - [ ] `/src/screens/Activity/TallyItem.jsx` - Check for issues with avatar display

- [ ] **Testing:**
  - [ ] Test with various network conditions
  - [ ] Test with empty cache scenario
  - [ ] Test across all screens that display avatar images
  - [ ] Test certificate views with both cached and non-cached images

## Technical Approach

1. **Enhanced Redux State for Avatar Images:**

```javascript
// avatarSlice.js
const initialState = {
  imagesByDigest: {}, // { [digest]: string }
  loadingStatus: {}, // { [digest]: 'idle' | 'loading' | 'succeeded' | 'failed' }
  error: {} // { [digest]: string | null }
};

// New thunk for fetching a specific image by digest
export const fetchImageByDigest = createAsyncThunk(
  'avatar/fetchImageByDigest',
  async (digest, { getState }) => {
    const state = getState();
    const imagesByDigestState = state.avatar?.imagesByDigest ?? {};
    
    // Skip if already in cache
    if (imagesByDigestState[digest]) {
      return imagesByDigestState;
    }
    
    // Try loading from AsyncStorage first
    try {
      const storageValue = await AsyncStorage.getItem(localStorage.TallyPictures);
      const cachedImages = JSON.parse(storageValue || '{}');
      
      if (cachedImages[digest]) {
        return {
          ...imagesByDigestState,
          [digest]: cachedImages[digest]
        };
      }
    } catch (err) {
      console.log('Error reading from AsyncStorage:', err);
    }
    
    // If not in AsyncStorage, fetch from backend
    try {
      // Determine if it's a holder image or tally file
      // This logic needs refinement based on how to identify the type
      const isHolder = true; // This needs to be determined somehow
      
      let fileData;
      if (isHolder) {
        fileData = await getHolderImage(null, digest);
      } else {
        // Need tally_seq here - might require adjustment to function signature
        fileData = await fetchTallyFile(null, digest, null);
      }
      
      if (fileData?.[0]) {
        const fileData64 = fileData[0]?.file_data64;
        const file_fmt = fileData[0]?.file_fmt;
        
        const image = `data:${file_fmt};base64,${fileData64}`;
        
        // Update AsyncStorage
        const updatedCache = { ...cachedImages, [digest]: image };
        await AsyncStorage.setItem(localStorage.TallyPictures, JSON.stringify(updatedCache));
        
        return {
          ...imagesByDigestState,
          [digest]: image
        };
      }
    } catch (err) {
      throw err;
    }
    
    return imagesByDigestState;
  }
);
```

2. **Create a Hook for Avatar Image Loading:**

```javascript
// src/hooks/useAvatarImage.js
import { useEffect } from 'react';
import { useSelector, useDispatch } from 'react-redux';
import { fetchImageByDigest } from '../redux/avatarSlice';

export const useAvatarImage = (digest) => {
  const dispatch = useDispatch();
  const { imagesByDigest, loadingStatus, error } = useSelector(state => state.avatar);
  
  const imageUri = digest ? imagesByDigest[digest] : null;
  const isLoading = loadingStatus[digest] === 'loading';
  const loadError = error[digest];
  
  useEffect(() => {
    // If we have a digest but no image and not already loading
    if (digest && !imageUri && loadingStatus[digest] !== 'loading') {
      dispatch(fetchImageByDigest(digest));
    }
  }, [digest, imageUri, loadingStatus, dispatch]);
  
  return {
    imageUri,
    isLoading,
    error: loadError
  };
};
```

3. **Update the Avatar Component:**

```jsx
// Modified Avatar component
import React from 'react';
import { StyleSheet, Image, View, ActivityIndicator } from 'react-native';
import { ProfileImage } from '../SvgAssets/SvgAssets';
import { colors } from '../../config/constants';
import { useAvatarImage } from '../../hooks/useAvatarImage';

const Avatar = (props) => {
  // If props.digest is provided, use the hook to fetch the image
  // Otherwise, use props.avatar directly (for backward compatibility)
  const { imageUri, isLoading } = props.digest ? 
    useAvatarImage(props.digest) : 
    { imageUri: props.avatar, isLoading: false };
  
  if (isLoading) {
    return (
      <View style={[styles.image, props?.style ?? {}, { backgroundColor: colors.gray100, justifyContent: 'center', alignItems: 'center' }]}>
        <ActivityIndicator size="small" color={colors.blue} />
      </View>
    );
  }
  
  return imageUri ? (
    <Image
      source={{ uri: imageUri }}
      style={[styles.image, props?.style ?? {}]}
    />
  ) : (
    <View style={[styles.image, props?.style ?? {}, { backgroundColor: colors.white }]}>
      <ProfileImage />
    </View>
  );
};

// Same styles as before
const styles = StyleSheet.create({
  image: {
    width: 100,
    height: 100,
    borderRadius: 50,
  }
});

export default Avatar;
```

4. **Integration in TallyGraphic:**

Update TallyGraphic to use the Avatar component with the digest prop instead of processing the images itself.

5. **Update DefaultCertificate:**

Modify the image rendering to use the enhanced Avatar component, which will automatically handle loading and showing the image.

## Implementation Phases

1. **Phase 1: Redux and Hook Enhancement**
   - Enhance avatarSlice.js with better tracking and individual image fetching
   - Create useAvatarImage hook
   - Update Avatar component

2. **Phase 2: Component Integration**
   - Update TallyGraphic to use the new Avatar component
   - Modify DefaultCertificate to use the enhanced image loading

3. **Phase 3: Screen Updates**
   - Fix OpenTallyView and other screens with inconsistent avatar display
   - Ensure proper image fetching triggers throughout the app

4. **Phase 4: Testing and Refinement**
   - Test across different network conditions
   - Test edge cases (missing images, server errors)
   - Optimize performance and reduce unnecessary re-renders

## Implementation Attempts and Lessons Learned

Our first implementation attempt revealed several important insights:

1. **Wyseman Connection Issues**: 
   - The infinite loading spinner in OpenTallyView and certificate details suggests the image fetching might be getting stuck because the Wyseman connection (`wm`) is not properly available or authenticated in those contexts.
   - The home screen worked because it likely has a properly established connection when the component mounts.

2. **Memoization Challenges**:
   - We implemented memoized selectors with createSelector, but still encountered "Selector returned a different result" warnings.
   - This suggests we need to be more careful about selector factory functions and ensuring proper dependencies in useMemo hooks.

3. **Redux State Structure**:
   - Adding new state properties (loadingState, errors) to the avatarSlice requires careful initialization and null checking throughout the codebase.
   - The Redux cycle needs proper error boundaries to prevent crashes from propagating.

4. **Physical Device vs Emulator Differences**:
   - The behavior differed between emulator and physical device, with the physical device showing more issues.
   - Network conditions on physical devices can be more challenging and require more robust retry/timeout mechanisms.

5. **Backward Compatibility**:
   - Our implementation maintained backward compatibility by supporting both the old approach (passing avatar URI directly) and new approach (passing digest).
   - This dual-mode support requires careful testing in all components.

For the next implementation attempt, we should consider:

1. Adding proper logging to trace the flow of image fetching
2. Implementing timeouts to prevent infinite loading states
3. Adding fallback mechanisms for cases where images can't be fetched
4. Testing more thoroughly with network conditions that match real-world usage
5. Ensuring Wyseman connections are properly established before attempting image fetches
6. Implementing the changes more incrementally, with testing after each small change