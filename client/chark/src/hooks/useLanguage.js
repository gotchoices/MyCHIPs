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
    if (!messageText?.users_v_me) {
      wm.register('users_v_me' + Math.random(), 'mychips.users_v_me', (data, err) => {
        if (data) {
          addTextsToState('users_v_me', data, setMessageText)
        }
      })
   }
  }, []);
  
  return messageText?.users_v_me ?? {};
}

export const useTalliesMeText = (wm) => {
  const { messageText, setMessageText } = useMessageText();

  useEffect(() => {
    if(!messageText?.tallies_v_me) {
      wm.register('tallies_v_me' + Math.random(), 'mychips.tallies_v_me', (data, err) => {
        if (data) {
          addTextsToState('tallies_v_me', data, setMessageText)
        }
      })
    }
  }, [])

  return messageText?.tallies_v_me ?? {};
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

  return messageText?.chits_v_me ?? {};
}

export const useCharkText = (wm) => {
  const { messageText, setMessageText } = useMessageText();

  useEffect(() => {
    if(!messageText?.chark) {
      wm.register('chark' + Math.random(), 'mychips.chark', (data, err) => {
        if (data) {
          addTextsToState('chark', data, setMessageText)
        }
      })
    }
  }, [wm, setMessageText])

  return messageText?.chark ?? {};
}

export const useLiftsPayMeText = (wm) => {
  const { messageText, setMessageText } = useMessageText();

  useEffect(() => {
    if(!messageText?.lifts_v_pay_me) {
      wm.register('lifts_v_pay_me' + Math.random(), 'mychips.lifts_v_pay_me', (data, err) => {
        if (data) {
          addTextsToState('lifts_v_pay_me', data, setMessageText)
        }
      })
    }
  }, [wm, setMessageText])

  return messageText?.lifts_v_pay_me ?? {};
}

function addTextsToState(field, texts, setState) {
  setState((prev) => {
    return {
      ...prev,
      [field]: texts,
    }
  })
}



