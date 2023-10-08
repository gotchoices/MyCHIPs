import React, { useState, useEffect } from 'react';
import { View, Text, StyleSheet, TouchableOpacity, Animated, Alert } from 'react-native';
import Toast from 'react-native-toast-message';
import { useSelector, useDispatch } from 'react-redux';

import { colors } from '../../config/constants';
import useSocket from '../../hooks/useSocket';
import useInvite from '../../hooks/useInvite';
import { createTemplate, fetchContracts, acceptTally, offerTally } from '../../services/tally';
import TemplateItem from './TemplateItem';
import CustomTextInput from '../../components/CustomTextInput';
import { FilterSecondIcon, SearchIcon } from '../../components/SvgAssets/SvgAssets';
import FloatingActionButton from '../../components/FloadingActionButton';
import BottomSheetModal from '../../components/BottomSheetModal';
import CommentContent from './CommentContent';
import LimitContent from './LimitContent';
import SuccessContent from '../../components/SuccessContent';
import { GenerateKeysDialog } from '../Tally/TallyPreview/GenerateKeysDialog';
import TallyEntryModal from './TallyEntryModal';

import useMessageText from '../../hooks/useMessageText';
import { useHoldTermsText } from '../../hooks/useLanguage';
import { fetchTemplates } from '../../redux/workingTalliesSlice';
import { fetchImagesByDigest } from '../../redux/avatarSlice';
import { createSignature, verifySignature } from '../../utils/message-signature';

const Header_Height = 160;

const useSearchData = (initialData) => {
  const [searchValue, setSearchValue] = useState('');
  const [filteredData, setFilteredData] = useState(initialData);

  useEffect(() => {
    if (searchValue) {
      const filtered = initialData.filter((item) => {
        const userName = item.part_cert?.name;
        const name = `${userName?.first}${userName?.middle ? ' ' + userName?.middle + ' ' : ''} ${userName?.surname}`
        return name.toLowerCase().includes(searchValue.toLowerCase());
      });
      setFilteredData(filtered);
    } else {
      setFilteredData(initialData);
    }
  }, [searchValue, initialData]);

  return { searchValue, setSearchValue, filteredData };
};

const EmptyContent = () => {
  return <View style={{ flex: 1, alignItems: 'center', alignContent: 'center' }}>
    <Text>No Tallies Found with the status.</Text>
  </View>
}

const TallyInvite = (props) => {
  const { fetching, tallies: data, imageFetchTrigger } = useSelector(state => state.workingTallies);
  const { imagesByDigest } = useSelector(state => state.avatar);
  const { searchValue, setSearchValue, filteredData } = useSearchData(data);
  const { wm, ws, tallyNegotiation } = useSocket();
  const [accepting, setAccepting] = useState(false);
  const [offering, setOffering] = useState(false);
  const [showGenerateKeyDialog, setShowGenerateKeyDialog] = useState(false);

  const { triggerInviteFetch } = useInvite();
  const { filter } = useSelector(state => state.profile);
  const [showCommentModal, setShowCommentModal] = useState(false);
  const [showLimitModal, setShowLimitModal] = useState(false);
  const [showTemplateSuccess, setShowTemplateSuccess] = useState(false)
  const [showAcceptSuccess, setShowAcceptSuccess] = useState(false)
  const [tallyItem, setTallyItem] = useState({});
  const [contract, setContract] = useState();
  const dispatch = useDispatch();
  const [negotiationData, setNegotiationData] = useState({
    showModal: false,
    data: undefined,
  });

  useHoldTermsText(wm);
  const { messageText } = useMessageText();
  const draftLang = messageText?.terms_lang?.request?.values?.find(item => item.value === 'draft');

  useEffect(() => {
    if (ws) {
      getTemplates();
    }
  }, [ws, triggerInviteFetch, filter, tallyNegotiation]);

  useEffect(() => {
    fetchContracts(wm, {
      fields: ['name', 'language', 'host', 'rid'],
      where: {
        top: true,
        name: 'Tally_Contract',
      },
    }).then((data) => {
      if(data?.[0]) {
        setContract(data[0])
      }
    }).catch(err => {
      console.log('Error fetching contract', err.message)
    })
  }, [wm])

  useEffect(() => {
    if(wm) {
      dispatch(fetchImagesByDigest({ wm, status: 'working' }))
    }
  }, [wm, imageFetchTrigger])

  const getFilterResult = (filterBy, separatedBy) => {
    const values = Object.values(filter);
    const selectedValues = values.filter((item) => item.selected);
    const entry = selectedValues.length === 0
      ? values.map((item) => item?.[filterBy]).join(separatedBy)
      : selectedValues.map((item) => item?.[filterBy]).join(separatedBy);
    return entry;
  }

  //Create a new template
  const newTemplate = (item) => {
    const rid = contract?.rid ?? '';

    const payload = {
      contract: { source: rid },
      comment: item.comment ?? 'Test: ' + new Date(),
      tally_type: item.tally_type,
      hold_terms: {
        call: 30,
        limit: item.tally_type === 'foil' ? item.limit : null
      },
      part_terms: {
        call: 30,
        limit: item.tally_type === 'stock' ? item.limit : null
      },
    }
    createTemplate(wm, payload).then((data) => {
      setShowTemplateSuccess(true);
      getTemplates()
    }).catch(err => {
      Toast.show({
        type: 'error',
        text1: err?.message ?? 'Error creating new template',
      });
    })
  }

  const getTemplates = () => {
    const entry = getFilterResult('status', ' ');
    dispatch(fetchTemplates({ wm, entry }))
  }

  const onNeogitationModalClose = () => {
    setNegotiationData({
      showModal: false,
      data: undefined,
    })
  }

  const showGenerateKey = () => {
    setShowGenerateKeyDialog(true)
  }

  const resetNegotiationData = () => {
    setNegotiationData({
      showModal: false,
      data: undefined,
    })
  }

  /**
    * @param {object} args
    * @param {number} args.tally_ent
    * @param {number} args.tally_seq
    * @param {number} args.tally_uuid
    */
  const onOffer = async ({ tally_uuid, tally_ent, tally_seq }) => {
    setOffering(true);
    offerTally(wm, {
      tally_uuid,
      tally_ent,
      tally_seq,
    }).then(() => {
      Toast.show({
        type: 'success',
        text1: 'Offer is processed.',
      });
    }).catch(err => {
      Toast.show({
        type: 'error',
        text1: err.message,
      });
    }).finally(() => {
      setOffering(false)
    })
  }

  /**
    * @param {object} args
    * @param {number} args.tally_ent
    * @param {number} args.tally_seq
    * @param {string} args.signature
    * @param {string} args.json
    */
  const onAccept = async ({ tally_ent, tally_seq, json }) => {
    setAccepting(true);
    createSignature(JSON.stringify(json)).then(signature => {
      return acceptTally(
        wm, { tally_ent, tally_seq, signature },
      );
    }).then((result) => {
      setShowAcceptSuccess(true);
      resetNegotiationData();
    }).catch(err => {
      const { isKeyAvailable, message } = err;
      if (isKeyAvailable === false) {
        Alert.alert(
          "Create Keys",
          "Seems like there is no key to create signature please continue to create one and accept tally.",
          [
            { text: "Cancel" },
            { text: "Continue", onPress: showGenerateKey }
          ]
        );
      } else {
        Alert.alert("Error", message || err);
      }
    }).finally(() => {
      setAccepting(false);
    });
  }

  const renderItem = ({ item, index }) => {
    return (
      <TemplateItem
        testID={`tally-${index}`}
        template={item}
        navigation={props.navigation}
        onItemSelected={item => {
          const hasPartCert = !!item?.part_cert;
          const canShare = !hasPartCert && item.status === 'draft';
          const canOffer = hasPartCert && item.status === 'draft';
          const canAccept = hasPartCert && item.status === 'offer';
          const first = item.part_cert?.name?.first;
          const middle = item.part_cert?.name?.middle;
          const surname = item.part_cert?.name?.surname;
          const name = item.part_cert?.type === 'o'
              ? `${item.part_cert?.name}`
              : `${first}${middle ? ' ' + middle: '' }${surname ? ' ' + surname : ''}`
          const limit = item.part_terms?.limit ?? 0;
          const holdDigest = item.hold_cert?.file?.[0]?.digest;
          const partDigest = item.part_cert?.file?.[0]?.digest;
          const tally_uuid = item?.tally_uuid;

          if(canOffer || canAccept) {
            setNegotiationData({
              showModal: true,
              data: {
                name,
                limit,
                canShare,
                canOffer,
                canAccept,
                partDigest,
                holdDigest,
                tally_uuid,
                json: item.json,
                tally_seq: item.id,
                tallyType: item.tally_type,
                tally_ent: item.tally_ent,
              }
            });
            return;
          }

          props.navigation.navigate('TallyPreview', {
            tally_seq: item.id,
            tally_ent: item.tally_ent,
          });
        }}
        draftLang={draftLang?.title ?? "Draft"}
      />
    )
  }

  const onFilter = () => {
    props.navigation.navigate("FilterScreen");
  }

  const onReview = (tally_seq, tally_ent) => {
    props.navigation.navigate('TallyPreview', {
      tally_seq,
      tally_ent,
    });

    resetNegotiationData();
  }

  const onTallyOpenDone = () => {
    props.navigation.navigate('Home');
  }

  const scrollY = new Animated.Value(0);
  const diffClampScrollY = Animated.diffClamp(scrollY, 0, Header_Height);
  const headerY = diffClampScrollY.interpolate({
    inputRange: [0, Header_Height],
    outputRange: [0, -Header_Height],
    extrapolate: 'clamp'
  });

  return (
    <>
      <View style={styles.container}>
        <Animated.View style={[styles.header, { transform: [{ translateY: headerY }] }]}>
          <Text style={styles.h1}>Working Tallies</Text>
          <View style={[styles.row, { marginVertical: 22 }]}>
            <Text style={styles.title}>{getFilterResult('title', ' | ')}</Text>
            <TouchableOpacity style={styles.filterContainer} onPress={onFilter}>
              <FilterSecondIcon />
              <Text style={styles.filterText}>Filters</Text>
            </TouchableOpacity>
          </View>
          <CustomTextInput
            placeholder="Search"
            value={searchValue}
            onChangeText={setSearchValue}
            leadingIcon={<SearchIcon size={16} />}
          />
        </Animated.View>

        <Animated.FlatList
          bounces={false}
          ListHeaderComponent={<View style={{ height: Header_Height, marginTop: 8 }} />}
          contentContainerStyle={{ paddingHorizontal: 16, paddingBottom: 16, backgroundColor: colors.white }}
          data={filteredData}
          renderItem={renderItem}
          refreshing={fetching}
          onRefresh={() => getTemplates()}
          keyExtractor={(item, index) => `${item?.tally_uuid}${index}`}
          ItemSeparatorComponent={() => <View style={{ height: 16 }} />}
          scrollEventThrottle={2}
          ListEmptyComponent={fetching ? <></> : <EmptyContent />}
          onScroll={Animated.event(
            [{
              nativeEvent: { contentOffset: { y: scrollY } }
            }],
            {
              useNativeDriver: false,
            }
          )}
          progressViewOffset={150}
        />
        <FloatingActionButton onPress={() => setShowCommentModal(true)} />
      </View>

      <BottomSheetModal
        isVisible={showCommentModal}
        onClose={() => setShowCommentModal(false)}
      >
        <CommentContent
          onNext={(item) => {
            setTallyItem({ ...tallyItem, ...item })
            setShowCommentModal(false);
            setShowLimitModal(true);
          }}
          onDismiss={() => {
            setShowCommentModal(false);
          }}
        />
      </BottomSheetModal>

      <BottomSheetModal
        isVisible={showLimitModal}
        onClose={() => setShowLimitModal(false)}
      >
        <LimitContent
          onNext={(item) => {
            setShowLimitModal(false);
            newTemplate({ ...tallyItem, ...item });
          }}
          onDismiss={() => {
            setShowLimitModal(false);
          }}
        />
      </BottomSheetModal>

      <BottomSheetModal
        isVisible={showTemplateSuccess}
        onClose={() => setShowTemplateSuccess(false)}
      >
        <SuccessContent
          message="Your tally has been created"
          onDone={() => setShowTemplateSuccess(false)}
          onDismiss={() => setShowTemplateSuccess(false)}
        />
      </BottomSheetModal>

      <BottomSheetModal
        isVisible={showAcceptSuccess}
        onClose={() => setShowAcceptSuccess(false)}
      >
        <SuccessContent
          buttonTitle="View"
          message="Your tally is now open"
          onDone={onTallyOpenDone}
          onDismiss={() => setShowAcceptSuccess(false)}
        />
      </BottomSheetModal>

      <BottomSheetModal
        isVisible={negotiationData.showModal}
        onClose={onNeogitationModalClose}
      >
        <TallyEntryModal
          onNeogitationModalClose={onNeogitationModalClose}
          negotiationData={negotiationData}
          onReview={onReview}
          onOffer={onOffer}
          onAccept={onAccept}
          accepting={accepting}
          offering={offering}
        />
      </BottomSheetModal>

      <GenerateKeysDialog
        visible={showGenerateKeyDialog}
        onDismiss={() => setShowGenerateKeyDialog(false)}
        onError={(err) => {
          Alert.alert("Error", err);
        }}
        onKeySaved={() => {
          Alert.alert("Success", "Key is generated successfully now you can accept tally.");
        }}
      />

    </>
  );
}

const styles = StyleSheet.create({
  container: {
    flex: 1,
    backgroundColor: colors.white,
  },
  title: {
    fontSize: 16,
    color: colors.gray300,
    fontFamily: 'inter'
  },
  row: {
    flexDirection: 'row',
    justifyContent: 'space-between',
    alignItems: 'center'
  },
  filterContainer: {
    borderWidth: 1,
    borderColor: colors.white100,
    backgroundColor: colors.white200,
    flexDirection: 'row',
    borderRadius: 20,
    paddingHorizontal: 12,
    paddingVertical: 3,
    justifyContent: 'center',
    alignItems: 'center'
  },
  filterText: {
    fontSize: 12,
    color: '#636363',
    marginStart: 4,
    fontFamily: 'inter',
  },
  header: {
    position: 'absolute',
    left: 0,
    right: 0,
    top: 0,
    height: Header_Height,
    backgroundColor: colors.white,
    zIndex: 1000,
    justifyContent: 'center',
    paddingHorizontal: 16,
  },
  h1: {
    fontSize: 18,
    fontFamily: 'inter',
    fontWeight: '500',
    color: '#636363',
    alignSelf: 'center',
  },
})

export default TallyInvite;
