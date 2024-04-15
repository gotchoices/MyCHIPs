import { useEffect } from 'react';

const useTitle = (navigation, title) => {
  useEffect(() => {
    if(title) {
      navigation.setOptions({
        title,
      });
    }
  }, [title])
}

export default useTitle;
