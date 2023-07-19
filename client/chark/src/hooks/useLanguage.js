import { useEffect } from 'react';

import useMessageText from './useMessageText';
import { getTallyText } from '../services/tally';

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

export const useCommunication = (wm) => {
  const { messageText, setMessageText } = useMessageText();

  useEffect(() => {
    wm.register('comm_lang' + Math.random(), 'base.comm_v_flat', (data, err) => {
      if(data) {
        addTextsToState('comm', data.col, setMessageText)
      }
    })
  }, [])

  return messageText?.comm ?? {};
}

export const useAddressV = (wm) => {
  const { messageText, setMessageText } = useMessageText();

  useEffect(() => {
    wm.register('addr_v' + Math.random(), 'base.addr_v', (data, err) => {
      if(data) {
        addTextsToState('addr_v', data.col, setMessageText)
      }
    })
  }, [wm, setMessageText])

  return messageText?.addr_v ?? {};
}

export const useAddressVFlat = (wm) => {
  const { messageText, setMessageText } = useMessageText();

  useEffect(() => {
    wm.register('addr_v_flat' + Math.random(), 'base.addr_v_flat', (data, err) => {
      if(data) {
        addTextsToState('addr_v_flat', data.col, setMessageText)
      }
    })
  }, [wm, setMessageText])

  return messageText?.addr_v_flat ?? {};
}

export const useExchange = (wm) => {
  const { messageText, setMessageText } = useMessageText();

  useEffect(() => {
    wm.register('exchange' + Math.random(), 'base.exchange', (data, err) => {
      if(data) {
        addTextsToState('exchange', data.col, setMessageText)
      }
    })
  }, [wm, setMessageText])

  return messageText?.exchange ?? {};
}

export const useUser = (wm) => {
  const { messageText, setMessageText } = useMessageText();

  useEffect(() => {
    wm.register('user_lang' + Math.random(), 'mychips.users_v_me', (data, err) => {
      if(data) {
        addTextsToState('users', data.col, setMessageText)
      }
    })
  }, [])

  return messageText?.users ?? {};
}

function addTextsToState(field, texts, setState) {
  setState((prev) => {
    return {
      ...prev,
      [field]: texts,
    }
  })
}
