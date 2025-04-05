import React, { useMemo } from 'react';
import {
  View,
  TextInput,
  StyleSheet,
  TouchableOpacity,
  Text,
} from 'react-native';
import {useSelector} from 'react-redux';

import Avatar from '../../components/Avatar';
import {colors} from '../../config/constants';
import HelpText from '../../components/HelpText';
import useMessageText from '../../hooks/useMessageText';

import {
  SwapIcon,
  UpArrowIcon,
  DownArrowIcon,
  LeftArrowIcon,
  RightArrowIcon,
} from '../../components/SvgAssets/SvgAssets';
import {round} from '../../utils/common';
import IconTooltip from '../../components/IconTooltip';

const TallyGraphic = props => {
  const {imagesByDigest} = useSelector(state => state.avatar);
  const partDigest = props.partCert?.file?.[0]?.digest;
  const holdDigest = props.holdCert?.file?.[0]?.digest;
  const tallyType = props.tallyType;
  const partImage = imagesByDigest[partDigest];
  const holdImage = imagesByDigest[holdDigest];

  const canEdit = props.canEdit ?? true;

  const holdCUIDAgent = props.holdCert?.chad?.cuid
    ? props.holdCert?.chad?.cuid + ':' + props.holdCert?.chad?.agent 
    : '';

  const partCUIDAgent = props.partCert?.chad?.cuid
    ? props.partCert?.chad?.cuid + ':' + props.partCert?.chad?.agent
    : '';


  const holdText = props.holdCert?.chad?.cuid + '...';
  const partText = props.partCert?.chad?.cuid ?? ''+ '...';

  const holdLimit = props?.holdTerms?.limit;
  const partLimit = props?.partTerms?.limit;

  const { messageText } = useMessageText();
  const talliesMessageText = messageText?.tallies_v_me?.msg;
  const talliesMeText = messageText?.tallies_v_me?.col;

  const holdLimitText = useMemo(() => {
    return talliesMeText?.hold_terms?.values?.find(hold => hold.value === 'limit');
  }, [talliesMeText?.hold_terms?.values])

  const partLimitText = useMemo(() => {
    return talliesMeText?.part_terms?.values?.find(hold => hold.value === 'limit');
  }, [talliesMeText?.part_terms?.values])


  const tallyTypeText = useMemo(() => {
    return talliesMeText?.tally_type?.values?.reduce((acc, current) => {
      acc[current.value] = current;
      return acc;
    }, {})
  })

  const limitText = useMemo(() => {
    return talliesMeText?.hold_terms?.values?.find((term) => term.value === 'limit')
  }, [talliesMeText?.hold_terms?.values])

  const onSwitchClick = () => {
    props?.setTallyType?.(prev => {
      const switchTally = {
        foil: 'stock',
        stock: 'foil',
      };

      return switchTally[prev];
    });
  };

  const onBlurLimit = () => {
    if (holdLimit && holdLimit.indexOf('.') >= 0) {
      props.onHoldTermsChange('limit')(round(holdLimit, 3));
    }

    if (partLimit && partLimit.indexOf('.') >= 0) {
      props.onPartTermsChange('limit')(partLimit);
    }
  };


  return (
    <View style={styles.main}>
      <View style={styles.wrapper}>
        <View style={[styles.rowWrapper, { marginBottom: -25 }]}>
          <View style={styles.leftIcon}>
            <HelpText
              label={talliesMessageText?.risk?.title ?? 'risk_title'}
              style={[styles.leftText, styles.leftTopText]}
            />

            <DownArrowIcon />
          </View>

          <View style={styles.topCenterWrapper}>
            <HelpText
              helpText={tallyTypeText?.foil?.help ?? ''}
              label={tallyTypeText?.foil?.title ?? ''}
              style={styles.headerText}
              placement="bottom"
            />

            {tallyType === 'foil' ? (
              holdImage ? (
                <View style={styles.circle}>
                  <Avatar style={styles.circle} avatar={holdImage} />
                </View>
              ) : (
                <Text style={styles.boldText}>{holdText}</Text>
              )
            ) : partImage ? (
              <View style={styles.circle}>
                <Avatar style={styles.circle} avatar={partImage} />
              </View>
            ) : (
              <Text style={styles.boldText}>{partText}</Text>
            )}
          </View>

          <View style={[styles.rightIcon]}>
            <LeftArrowIcon />

            <HelpText
              label={talliesMessageText?.credit?.title ?? 'credit_title'}
              style={[styles.rightText, styles.rightTopText]}
            />
          </View>
        </View>
      </View>

      <View style={styles.midView}>
        <View style={styles.midRow}>
          <View style={{ width: '25%', flexDirection: 'row' }}>
            <TextInput
              maxLength={9}
              placeholder={props.net ?? ''}
              editable={canEdit}
              value={tallyType === 'foil' ? holdLimit : partLimit}
              keyboardType="numeric"
              style={styles.input}
              onBlur={onBlurLimit}
              onChangeText={text => {
                tallyType === 'foil'
                  ? props.onHoldTermsChange('limit')(text)
                  : props.onPartTermsChange('limit')(text);
              }}
            />

            <IconTooltip text={tallyType === 'foil' ? holdLimitText?.help ?? '' : partLimitText?.help ?? ''} />
          </View>

          <View style={{ width: '50%', alignItems: 'center' }}>
            <HelpText label={limitText?.title ?? ''} style={styles.midText} />
          </View>

          <View style={{ width: '25%', flexDirection: 'row' }}>
            <IconTooltip text={tallyType === 'stock' ? holdLimitText?.help : partLimitText?.help} />

            <TextInput
              maxLength={9}
              editable={canEdit}
              placeholder={props.amount ?? ''}
              value={tallyType === 'stock' ? holdLimit : partLimit}
              keyboardType="numeric"
              style={styles.input}
              onBlur={onBlurLimit}
              onChangeText={text => {
                tallyType === 'stock'
                  ? props.onHoldTermsChange('limit')(text)
                  : props.onPartTermsChange('limit')(text);
              }}
            />
          </View>
        </View>
      </View>

      <View style={styles.wrapper}>
        <View style={[styles.rowWrapper, { marginTop: -25 }]}>
          <View style={styles.leftIcon}>
            <HelpText
              label={talliesMessageText?.credit?.title ?? 'credit_title'}
              style={[styles.leftText, styles.leftBottomText]}
            />
            <RightArrowIcon />
          </View>

          <View style={styles.bottomCenterWrapper}>
            {tallyType === 'stock' ? (
              holdImage ? (
                <View style={styles.circle}>
                  <Avatar style={styles.circle} avatar={holdImage} />
                </View>
              ) : (
                <Text style={styles.boldText}>{holdText}</Text>
              )
            ) : partImage ? (
              <View style={styles.circle}>
                <Avatar style={styles.circle} avatar={partImage} />
              </View>
            ) : (
              <Text style={styles.boldText}>{partText}</Text>
            )}

            <HelpText
              helpText={tallyTypeText?.stock?.help ?? ''}
              label={tallyTypeText?.stock?.title ?? ''}
              style={styles.headerText}
            />

          </View>

          <View style={styles.rightIcon}>
            <UpArrowIcon />
            <HelpText
              label={talliesMessageText?.risk?.title ?? 'risk_title'}
              style={[styles.rightText, styles.rightBottomText]}
            />
          </View>
        </View>
      </View>

      {canEdit && (
        <View style={styles.absoluteView}>
          <TouchableOpacity onPress={onSwitchClick}>
            <SwapIcon />
          </TouchableOpacity>
        </View>
      )}
    </View>
  );
};

const arrowText = {
  color: 'black',
  fontSize: 12,
  fontWeight: '500',
};

const styles = StyleSheet.create({
  main: {
    flex: 1,
    //marginTop: 25,
    paddingTop: 24,
    //marginHorizontal: 40,
    alignItems: 'center',
  },
  circle: {
    height: 70,
    width: 70,
    borderRadius: 50,
    backgroundColor: colors.gray700,
  },
  headerText: {
    marginLeft: 14,
    paddingTop: 10,
    fontWeight: '400',
    textAlign: 'center',
    color: colors.dimgray,
  },
  midText: {
    fontWeight: '400',
    textAlign: 'center',
    color: colors.dimgray,
  },
  bottomCenterWrapper: {
    height: 100,
    marginBottom: -75, 
    //marginBottom: -25,
    alignItems: 'center',
    justifyContent: 'center',
  },
  topCenterWrapper: {
    height: 100,
    //marginBottom: 80,
    marginTop: -75,
    alignItems: 'center',
    justifyContent: 'center',
  },
  rowWrapper: {
    width: '80%',
    flexDirection: 'row',
  },
  midRow: {
    flexDirection: 'row',
    alignItems: 'center',
    justifyContent: 'space-between',
  },
  input: {
    width: '90%',
    padding: 10,
    borderRadius: 5,
    borderWidth: 0.5,
    //marginHorizontal: 30,
    borderColor: colors.dimgray,
  },
  leftIcon: {
    width: '33%',
    flexDirection: 'row',
    alignItems: 'center',
    justifyContent: 'center',
  },
  rightIcon: {
    width: '33%',
    flexDirection: 'row',
    alignItems: 'center',
    justifyContent: 'center',
  },
  leftText: {
    ...arrowText,
    color: colors.black,
  },
  rightText: {
    ...arrowText,
    color: colors.black,
  },
  leftTopText: {
  },
  leftBottomText: {
  },
  rightTopText: {
  },
  rightBottomText: {
  },
  absoluteView: {
    top: 0,
    right: 0,
    position: 'absolute',
  },
  boldText: {
    color: colors.black,
    fontSize: 16,
    fontWeight: 'bold',
    textDecorationStyle: 'solid',
    textDecorationLine: 'underline',
  },
  wrapper: {
    height: 100,
    alignItems: 'center',
    justifyContent: 'center',
  },
});

export default TallyGraphic;
