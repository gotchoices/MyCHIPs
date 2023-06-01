import { useEffect } from 'react';

import useMessageText from './useMessageText';
import { getTallyText } from '../services/tally';
import { getProfileText} from '../services/profile';

export const useTallyText = (wm) => {
  const { messageText, setMessageText } = useMessageText();

  useEffect(() => {
    if(wm && !messageText?.tallies) {
      getTallyText(wm).then(tallies => {
        setMessageText((prev) => {
          return {
            ...prev,
            tallies,
          }
        })
      })
    }
  }, [wm, messageText?.tallies])

  return messageText?.tallies ?? {};
}

export const useProfileText = (wm) => {
  const { messageText, setMessageText } = useMessageText();

  useEffect(() => {
    if(wm && !messageText?.profile) {
      getProfileText(wm).then(profile => {
        console.log('profile', profile)
        setMessageText((prev) => {
          return {
            ...prev,
            profile,
          }
        });
      })
    }
  }, [wm, messageText?.profile])

  return messageText?.profile ?? {};
}
