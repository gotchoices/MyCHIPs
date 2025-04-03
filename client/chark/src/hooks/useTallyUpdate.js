import { useEffect, useState } from 'react';
import { useDispatch } from 'react-redux';

import { fetchTallies } from '../services/tally';
import useSocket from '../hooks/useSocket';
import { getTallyValidityStatus } from '../utils/tally-verification';
import { updateTallyValidityStatus } from '../redux/openTalliesSlice';

const useTallyUpdate = (wm, tally_seq, tally_ent) => {
  const { tallyNegotiation } = useSocket();
  const dispatch = useDispatch();
  const [refreshing, setRefreshing] = useState(false);
  const [loading, setLoading] = useState(true);
  const [tally, setTally] = useState();
  const [tallyType, setTallyType] = useState('stock');
  const [contract, setContract] = useState('');
  const [holdTerms, setHoldTerms] = useState({
    limit: undefined,
    call: undefined,
  });
  const [partTerms, setPartTerms] = useState({
    limit: undefined,
    call: undefined,
  });
  const [comment, setComment] = useState(comment);
  const [initialFields, setInitialFields] = useState({
    comment: '',
    contract: '',
    tallyType: '',
    holdLimit: undefined,
    partLimit: undefined,
  })


  useEffect(() => {
    if (wm || (tallyNegotiation?.reason === 'draft' && tallyNegotiation?.state === 'P.draft')) {
      fetchTally();
    }
  }, [wm, tally_seq, tally_ent, tallyNegotiation])

  const fetchTally = (_refreshing = false) => {
    if (_refreshing) {
      setRefreshing(true);
    }

    fetchTallies(wm, {
      fields: ['tally_ent', 'tally_seq', 'tally_uuid', 'tally_date', 'status', 'hold_terms', 'part_terms', 'part_cert', 'tally_type', 'comment', 'contract', 'json_core', 'hold_sig', 'hold_cert', 'state'],
      where: {
        tally_ent,
        tally_seq,
      }
    }).then(data => {
      const _tally = data?.[0];
      if (_tally) {
        const tallyType = _tally.tally_type ?? '';
        const contract = _tally.contract?.source ?? '';
        const comment = _tally.comment ?? '';
        const holdLimit = _tally.hold_terms?.limit?.toString();
        const partLimit = _tally.part_terms?.limit?.toString();

        setTally(_tally);
        setTallyType(_tally.tally_type);
        setContract(contract);
        setComment(comment);
        setHoldTerms({
          limit: holdLimit,
          call: _tally.hold_terms?.call?.toString(),
        })
        setPartTerms({
          limit: partLimit,
          call: _tally.part_terms?.call?.toString(),
        })
        setInitialFields({
          comment,
          contract,
          holdLimit,
          partLimit,
          tallyType,
        })
        
        // Validate the tally and update Redux store with validation result
        getTallyValidityStatus(_tally).then(validityStatus => {
          dispatch(updateTallyValidityStatus({
            tallyUuid: _tally.tally_uuid,
            tallyEnt: _tally.tally_ent,
            tallySeq: _tally.tally_seq,
            validityStatus
          }));
        });
      }
    }).finally(() => {
      setLoading(false);
      setRefreshing(false);
    })
  }


  const onHoldTermsChange = (name) => {
    return (value) => {
      const regex = /(\..*){2,}/;
      if(regex.test(value)) {
        return;
      }

      setHoldTerms({
        ...holdTerms,
        [name]: value,
      })
    }
  }

  const onPartTermsChange = (name) => {
    return (value) => {
      const regex = /(\..*){2,}/;
      if(regex.test(value)) {
        return;
      }

      setPartTerms({
        ...partTerms,
        [name]: value,
      })
    }
  }

  return {
    loading,
    refreshing,
    tally,
    tallyType,
    contract,
    holdTerms,
    partTerms,
    comment,
    setComment,
    onHoldTermsChange,
    onPartTermsChange,
    setTallyType,
    setContract,
    fetchTally,
    setTally,
    initialFields,
    setInitialFields,
  }
}

export default useTallyUpdate;
