import { useEffect } from 'react';

import useMessageText from './useMessageText';

export const useTallyText = (wm) => {
  const { messageText, setMessageText } = useMessageText();

  useEffect(() => {
    if (!messageText?.tallies) {
      wm.register('tally_lang' + Math.random(), 'mychips.tallies', (data, err) => {
        if (data) {
          addTextsToState('tallies', data.col, setMessageText)
        }
      })
    }
  }, [wm, setMessageText])

  return messageText?.tallies ?? {};
}

export const useUserTalliesText = (wm) => {
  const { messageText, setMessageText } = useMessageText();

  useEffect(() => {
    if (!messageText?.userTallies) {
      wm.register('user_tally_lang' + Math.random(), 'mychips.users_v_tallies', (data, err) => {
        if (data) {
          addTextsToState('userTallies', data.col, setMessageText)
        }
      })
    }
  }, [wm, setMessageText])

  return messageText?.userTallies ?? {};
}

export const useCommunication = (wm) => {
  const { messageText, setMessageText } = useMessageText();

  useEffect(() => {
    if (!messageText?.comm) {
      wm.register('comm_lang' + Math.random(), 'base.comm_v_flat', (data, err) => {
        if (data) {
          addTextsToState('comm', data.col, setMessageText)
        }
      })
    }
  }, [])

  return messageText?.comm ?? {};
}

export const useAddressV = (wm) => {
  const { messageText, setMessageText } = useMessageText();

  useEffect(() => {
    if (!messageText?.addr_v) {
      wm.register('addr_v' + Math.random(), 'base.addr_v', (data, err) => {
        if (data) {
          addTextsToState('addr_v', data.col, setMessageText)
        }
      })
    }
  }, [wm, setMessageText])

  return messageText?.addr_v ?? {};
}

export const useAddressVFlat = (wm) => {
  const { messageText, setMessageText } = useMessageText();

  useEffect(() => {
    if (!messageText?.addr_v_flat) {
      wm.register('addr_v_flat' + Math.random(), 'base.addr_v_flat', (data, err) => {
        if (data) {
          addTextsToState('addr_v_flat', data.col, setMessageText)
        }
      })
    }
  }, [wm, setMessageText])

  return messageText?.addr_v_flat ?? {};
}

export const useExchange = (wm) => {
  const { messageText, setMessageText } = useMessageText();

  useEffect(() => {
    if (!messageText?.exchange) {
      wm.register('exchange' + Math.random(), 'base.exchange', (data, err) => {
        if (data) {
          addTextsToState('exchange', data.col, setMessageText)
        }
      })
    }
  }, [wm, setMessageText])

  return messageText?.exchange ?? {};
}

export const useUser = (wm) => {
  const { messageText, setMessageText } = useMessageText();


  useEffect(() => {
    if (!messageText?.users) {
      wm.register('user_lang' + Math.random(), 'mychips.users_v_me', (data, err) => {
        if (data) {
          addTextsToState('users', data.col, setMessageText)
        }
      })
   }
  }, []);
  
  return messageText?.users ?? {};
}

export const useHoldTermsText = (wm) => {
  const { messageText, setMessageText } = useMessageText();

  useEffect(() => {
    wm.register('terms_lang' + Math.random(), 'mychips.tallies_v_me', (data, err) => {
      if (data) {
        addTextsToState('terms_lang', data.col, setMessageText)
      }
    })
  }, [])

  return messageText?.terms_lang ?? {};
}

export const useChitsMeText = (wm) => {
  const { messageText, setMessageText } = useMessageText();

  useEffect(() => {
    if(!messageText?.chits_v_me) {
      wm.register('chits_v_me' + Math.random(), 'mychips.chits_v_me', (data, err) => {
        if (data) {
          addTextsToState('chits_v_me', data, setMessageText)
        }
      })
    }
  }, [wm, setMessageText])

  return messageText ?? {};
}

function addTextsToState(field, texts, setState) {
  setState((prev) => {
    return {
      ...prev,
      [field]: texts,
    }
  })
}



