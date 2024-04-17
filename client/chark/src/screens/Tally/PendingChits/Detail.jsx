import React, { useState, useEffect } from 'react';
import { useSelector, useDispatch } from 'react-redux';
import {
  View,
  Text,
  TextInput,
  StyleSheet,
} from 'react-native';

import Header from './Header';
import HelpText from '../../../components/HelpText'
import { ChitIcon } from '../../../components/SvgAssets/SvgAssets';
import SwapIcon from '../../../../assets/svg/swap.svg';
import AcceptButton from './AcceptButton';
import RejectButton from './RejectButton';

import { colors } from '../../../config/constants';
import { getCurrencyRate } from '../../../redux/chipCurrencySlice';
import useSocket from '../../../hooks/useSocket';
import { round } from '../../../utils/common';
import useMessageText from '../../../hooks/useMessageText';

const PendingChitDetail = (props) => {
  const dispatch = useDispatch();
  const { wm } = useSocket();
  const { chit } = props.route.params ?? {};
  const [memo, setMemo] = useState(chit?.memo ?? '');
  const [swapped, setSwapped] = useState(false);

  const { messageText } = useMessageText()
  const chitsMeText = messageText?.chits_v_me?.col;
  const chitsMessageText = messageText?.chits_v_me?.msg;
  const charkText = messageText?.chark?.msg;

  const { preferredCurrency } = useSelector((state) => state.profile);
  const { conversionRate } = useSelector((state) => state.chipCurrency);
  const net_pc = (chit.net ?? 0) / 1000;
  let convertedNet = 0;

  const commonText = {
    rejected: chitsMessageText?.rejected,
    accepted: chitsMessageText?.approved,
    approve: chitsMessageText?.approve,
    reject: chitsMessageText?.reject,
    nokey: charkText?.nokey,
    cancel: charkText?.cancel,
    next: charkText?.next,
  }

  if(conversionRate) {
    convertedNet = round(conversionRate * net_pc, 2);
  }

  useEffect(() => {
    dispatch(getCurrencyRate({
      wm,
      currencyCode: preferredCurrency.code,
    }))
  }, [preferredCurrency?.code])

  const onBack = () => {
    props.navigation.goBack();
  }

  const onSwap = () => {
    setSwapped((prev) => !prev);
  }

  const onMemoChange = (text) => {
    setMemo(text);
  }

  return (
    <View style={styles.container}>
      <View style={{ marginBottom: 48 }}>
        <Header onBackPress={onBack}>
          <Text style={styles.headerText}>
            {chitsMessageText?.pending?.title ?? ''}
          </Text>
        </Header>
      </View>

      <View style={styles.body}>
        <View style={styles.netWrapper}>
          <View>
            {swapped ? (
              <SwappedChip
                net_pc={net_pc}
                convertedNet={convertedNet}
                code={preferredCurrency?.code}
              />
            ): (
              <NonSwappedChip
                net_pc={net_pc}
                convertedNet={convertedNet}
                code={preferredCurrency?.code}
              />
            )}
          </View>

          {!!preferredCurrency?.code && (
            <SwapIcon 
              style={{ marginLeft: 12 }}
              onPress={onSwap} 
            />
          )}
        </View>

        <TextInput
          multiline
          numberOfLines={6}
          value={memo}
          placeholder={chitsMeText?.memo?.title ?? ''}
          style={[styles.input, styles.comment]}
          onChangeText={onMemoChange}
        />

        <View style={styles.reference}>
          <HelpText
            style={styles.referenceText}
            label={chitsMeText?.reference?.title ?? ''}
          />
        </View>
      </View>

      {chit?.state === 'L.pend' && (
        <View style={styles.action}>
          <AcceptButton
            json={chit?.json_core}
            chit_ent={chit?.chit_ent}
            chit_seq={chit?.chit_seq}
            chit_idx={chit?.chit_idx}
            text={commonText}
          />

          <RejectButton
            chit_ent={chit?.chit_ent}
            chit_seq={chit?.chit_seq}
            chit_idx={chit?.chit_idx}
            style={styles.rejectBtn}
            text={commonText}
          />
        </View>
      )}
    </View>
  )
}

function SwappedChip(props) {
  return (
    <>
      {!!props.code && (
        <Text style={styles.convertedRate}>
          {props.convertedNet} {props.code}
        </Text>
      )}

      <View style={{ flexDirection: 'row', justifyContent: 'flex-end' }}>
        <ChitIcon color={colors.black} height={20} />
        <Text style={styles.currency}>
          {props.net_pc}
        </Text>
      </View>
    </>
  )
}

function NonSwappedChip(props) {
  return (
    <>
      <View style={styles.net}>
        <ChitIcon color={colors.black} height={53} width={26.5}/>
        <Text style={styles.chipRate}>
          {props.net_pc}
        </Text>
      </View>

      {!!props.code && (
        <Text style={styles.currency}>
          {props.convertedNet} {props.code}
        </Text>
      )}
    </>
  )
}

const font = {
  fontFamily: 'inter',
  fontWeight: '500',
}

const styles = StyleSheet.create({
  container: {
    flex: 1,
    marginHorizontal: 24,
  },
  headerText: {
    fontSize: 18,
    fontFamily: 'inter',
    fontWeight: '500',
    color: colors.gray300,
  },
  body: {
  },
  netWrapper: {
    flexDirection: 'row',
    justifyContent: 'center',
    alignItems: 'center',
    marginBottom: 32,
  },
  net: {
    flexDirection: 'row',
    alignItems: 'center',
  },
  currency: {
    ...font,
    fontSize: 14,
    fontWeight: '400',
    alignSelf: 'flex-end',
    color: colors.black,
  },
  chipRate: {
    ...font,
    color: colors.black,
    fontSize: 45,
    marginLeft: 5,
  },
  convertedRate: {
    ...font,
    color: colors.black,
    fontSize: 35,
    marginLeft: 5,
  },
  input: {
    padding: 10,
    borderWidth: 1,
    borderRadius: 5,
    textAlignVertical: 'top',
    borderColor: colors.gray,
    backgroundColor: colors.white,
    marginBottom: 32,
  },
  referenceText: {
    ...font,
    fontSize: 16,
    color: colors.gray300,
  },
  action: {
    flex: 1,
    justifyContent: 'flex-end',
    marginBottom: 28,
  },
  rejectBtn: {
    marginTop: 10,
    borderColor: colors.red,
    backgroundColor: colors.red,
  }
});

export default PendingChitDetail;
