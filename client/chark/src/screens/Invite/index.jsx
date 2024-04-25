import React, {useState, useEffect, useMemo} from 'react';
import {
  View,
  Text,
  StyleSheet,
  TouchableOpacity,
  Alert,
  TouchableHighlight,
} from 'react-native';
import Toast from 'react-native-toast-message';
import SwipeableFlatList from 'react-native-swipeable-list';
import {useSelector, useDispatch} from 'react-redux';

import { colors, toastVisibilityTime } from '../../config/constants';
import useSocket from '../../hooks/useSocket';
import useInvite from '../../hooks/useInvite';
import {
  createTemplate,
  fetchContracts,
  refuseTally,
} from '../../services/tally';
import TemplateItem from './TemplateItem';
import CustomTextInput from '../../components/CustomTextInput';
import {
  FilterSecondIcon,
  SearchIcon,
} from '../../components/SvgAssets/SvgAssets';
import FloatingActionButton from '../../components/FloadingActionButton';
import BottomSheetModal from '../../components/BottomSheetModal';
import CommentContent from './CommentContent';
import SuccessContent from '../../components/SuccessContent';
import TallyEntryModal from './TallyEntryModal';

import useMessageText from '../../hooks/useMessageText';
import {useTalliesMeText} from '../../hooks/useLanguage';
import {fetchTemplates} from '../../redux/workingTalliesSlice';
import {fetchImagesByDigest} from '../../redux/avatarSlice';
import {request} from '../../services/request';
import {random} from '../../utils/common';
import {getTallyName} from '../../utils/user';
import { showError } from '../../utils/error';

const Header_Height = 160;

const useSearchData = initialData => {
  const [searchValue, setSearchValue] = useState('');
  const [filteredData, setFilteredData] = useState(initialData);

  useEffect(() => {
    if (searchValue.length >= 2) {
      const filtered = initialData.filter(item => {
        const name = getTallyName(item);

        if (name) {
          return name.toLowerCase().includes(searchValue.toLowerCase());
        }
      });
      setFilteredData(filtered);
    } else {
      setFilteredData(initialData);
    }
  }, [searchValue, initialData]);

  return {searchValue, setSearchValue, filteredData};
};

const EmptyContent = () => {
  return (
    <View
      style={{
        flex: 1,
        alignItems: 'center',
        alignContent: 'center',
      }}>
      <Text>No Tallies Found with the status.</Text>
    </View>
  );
};

const TallyInvite = props => {
  const {
    fetching,
    tallies: data,
    imageFetchTrigger,
  } = useSelector(state => state.workingTallies);

  const {searchValue, setSearchValue, filteredData} = useSearchData(data);
  const {wm, ws, tallyNegotiation} = useSocket();

  /*
   * fromOffer: used to navigate after offering tally from tally preview
   */
  const {fromOffer} = props.route?.params ?? {};

  const {triggerInviteFetch} = useInvite();
  const {filter} = useSelector(state => state.profile);
  const [showCommentModal, setShowCommentModal] = useState(false);
  const [showTemplateSuccess, setShowTemplateSuccess] = useState(false);
  const [showAcceptSuccess, setShowAcceptSuccess] = useState(false);
  const [showOfferSuccess, setShowOfferSuccess] = useState({
    show: false,
    offerTo: '',
    tally_ent: null,
    tally_seq: null,
  });
  const [tallyItem, setTallyItem] = useState({});
  const [contract, setContract] = useState();
  const dispatch = useDispatch();
  const [negotiationData, setNegotiationData] = useState({
    showModal: false,
    data: undefined,
  });

  useTalliesMeText(wm);
  const {messageText} = useMessageText();
  const talliesColText = messageText?.tallies_v_me?.col;
  const charkText = messageText?.chark?.msg;

  const draftLang = useMemo(() => {
    return talliesColText?.request?.values?.find(
      item => item.value === 'draft',
    );
  }, [talliesColText?.request?.values]);

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
    })
      .then(data => {
        if (data?.[0]) {
          setContract(data[0]);
        }
      })
      .catch(err => {
        showError(err);
      });
  }, [wm]);

  // Fetch images(uses cache if already present)
  useEffect(() => {
    if (wm) {
      dispatch(fetchImagesByDigest({wm, status: 'working'}));
    }
  }, [wm, imageFetchTrigger]);

  useEffect(() => {
    if (fromOffer) {
      setShowOfferSuccess({
        show: fromOffer.show ?? false,
        offerTo: fromOffer.offerTo ?? '',
        tally_ent: fromOffer.tally_ent ?? null,
        tally_seq: fromOffer.tally_seq ?? null,
      });
    }
  }, [fromOffer]);

  const getFilterResult = (filterBy, separatedBy) => {
    const values = Object.values(filter);
    const selectedValues = values.filter(item => item.selected);
    const entry =
      selectedValues.length === 0
        ? values.map(item => item?.[filterBy]).join(separatedBy)
        : selectedValues.map(item => item?.[filterBy]).join(separatedBy);
    return entry;
  };

  //Create a new template
  const newTemplate = item => {
    const rid = contract?.rid ?? '';

    const payload = {
      contract: {source: rid},
      comment: item.comment ?? 'Test: ' + new Date(),
      tally_type: item.tally_type,
      hold_terms: {
        call: 30,
        limit: item.myLimit ?? null,
      },
      part_terms: {
        call: 30,
        limit: item.partnerLimit ?? null,
      },
    };
    createTemplate(wm, payload)
      .then(data => {
        setShowTemplateSuccess(true);
        getTemplates();
      })
      .catch(err => {
        showError(err);
      });
  };

  const getTemplates = () => {
    const entry = getFilterResult('status', ' ');
    dispatch(fetchTemplates({wm, entry}));
  };

  const onNeogitationModalClose = () => {
    setNegotiationData({
      showModal: false,
      data: undefined,
    });
  };

  const resetNegotiationData = () => {
    setNegotiationData({
      showModal: false,
      data: undefined,
    });
  };

  const postOffer = () => {
    const {tally_ent, tally_seq, name} = negotiationData?.data ?? {};
    setShowOfferSuccess({
      tally_ent,
      tally_seq,
      show: true,
      offerTo: name,
    });
    resetNegotiationData();
  };

  const postAccept = () => {
    setShowAcceptSuccess(true);
    resetNegotiationData();
  };

  const renderItem = ({item, index}) => {
    return (
      <View style={styles.itemView}>
        <TemplateItem
          testID={`tally-${index}`}
          template={item}
          navigation={props.navigation}
          onItemSelected={item => {
            const state = item?.state;
            const canShare = state === 'draft';
            const canOffer = state === 'P.draft';
            const canAccept = state === 'P.offer';
            const first = item.part_cert?.name?.first;
            const middle = item.part_cert?.name?.middle;
            const surname = item.part_cert?.name?.surname;
            const name =
              item.part_cert?.type === 'o'
                ? `${item.part_cert?.name}`
                : `${first}${middle ? ' ' + middle : ''}${
                    surname ? ' ' + surname : ''
                  }`;
            const limit = item.part_terms?.limit ?? 0;
            const holdDigest = item.hold_cert?.file?.[0]?.digest;
            const partDigest = item.part_cert?.file?.[0]?.digest;
            const tally_uuid = item?.tally_uuid;

            if (canOffer || canAccept) {
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
                  json_core: item.json_core,
                  tally_seq: item.id,
                  tallyType: item.tally_type,
                  tally_type: item.tally_type,
                  tally_ent: item.tally_ent,
                },
              });
              return;
            }

            props.navigation.navigate('TallyPreview', {
              tally_seq: item.id,
              tally_ent: item.tally_ent,
            });
          }}
          draftLang={draftLang?.title ?? 'draft'}
        />
      </View>
    );
  };

  const onFilter = () => {
    props.navigation.navigate('FilterScreen');
  };

  const onReview = (tally_seq, tally_ent) => {
    props.navigation.navigate('TallyPreview', {
      tally_seq,
      tally_ent,
    });

    resetNegotiationData();
  };

  const onTallyOpenDone = () => {
    props.navigation.navigate('Home');
  };

  const onDismissOfferSuccess = () => {
    props.navigation.setParams({
      fromOffer: null,
    });
    setShowOfferSuccess({
      show: false,
      offerTo: '',
      tally_ent: null,
      tally_seq: null,
    });
  };

  const onDoneOfferSuccess = () => {
    const tally_ent = showOfferSuccess?.tally_ent;
    const tally_seq = showOfferSuccess?.tally_seq;

    onDismissOfferSuccess();

    if (tally_ent && tally_seq) {
      props.navigation.navigate('TallyPreview', {
        tally_seq,
        tally_ent,
      });
    }
  };

  const onRefuse = item => {
    refuseTally(wm, item)
      .then(() => {
        Toast.show({
          type: 'success',
          text1: 'Tally refused.',
          visibilityTime: toastVisibilityTime,
        });
        props.navigation.goBack();
      })
      .catch(err => {
        showError(err);
      });
  };

  const deleteDraftTallies = item => {
    const spec = {
      view: 'mychips.tallies_v_me',
      where: {
        tally_ent: item.tally_ent,
        tally_seq: item.tally_seq,
      },
    };

    return request(wm, 'delete_tally' + random(), 'delete', spec)
      .then(res => {
        Toast.show({
          type: 'success',
          text1: charkText?.deleted?.help ?? '',
          visibilityTime: toastVisibilityTime,
        });
        getTemplates();
      })
      .catch(err =>{
        showError(err);
      });
  };

  const commonText = {
    comment: talliesColText?.comment,
    tally_type: talliesColText?.tally_type,
    next: charkText?.next,
    newtally: charkText?.newtally,
    hold_terms: talliesColText?.hold_terms,
    part_terms: talliesColText?.part_terms,
  };

  const onDeleteTally = item => {
    if (item.status === 'draft') {
      return deleteDraftTallies(item);
    }

    return onRefuse(item);
  };

  const renderRightAction = item => {
    return (
      <View style={styles.row}>
        <TouchableHighlight
          activeOpacity={0.6}
          onPress={() => onDeleteTally(item)}
          underlayColor={colors.red}
          style={[styles.rightActions, {backgroundColor: colors.red}]}>
          <Text style={{color: colors.white}}>void</Text>
        </TouchableHighlight>
      </View>
    );
  };

  return (
    <>
      <View style={styles.container}>
        <View style={styles.header}>
          <Text style={styles.h1}>{charkText?.working?.title ?? ''}</Text>
          <View
            style={[
              styles.row,
              {marginTop: 22, justifyContent: 'space-between'},
            ]}>
            <Text style={[styles.filterText, {fontSize: 16}]}>
              {draftLang?.title ?? ''}
            </Text>

            <TouchableOpacity style={styles.filterContainer} onPress={onFilter}>
              <FilterSecondIcon />
              <Text style={styles.filterText}>
                {talliesColText?.status?.title ?? ''}
              </Text>
            </TouchableOpacity>
          </View>
          <CustomTextInput
            placeholder={charkText?.search?.title ?? ''}
            value={searchValue}
            onChangeText={setSearchValue}
            leadingIcon={<SearchIcon size={16} />}
          />
        </View>

        <SwipeableFlatList
          ListHeaderComponent={
            <View style={{height: Header_Height, marginTop: 8}} />
          }
          data={filteredData}
          renderItem={renderItem}
          contentContainerStyle={styles.contentContainerStyle}
          refreshing={fetching}
          maxSwipeDistance={90}
          shouldBounceOnMount={true}
          showsVerticalScrollIndicator={false}
          renderQuickActions={({item}) => renderRightAction(item)}
          onRefresh={() => getTemplates()}
          keyExtractor={(item, index) => `${item?.tally_uuid}${index}`}
          ItemSeparatorComponent={() => <View style={{height: 16}} />}
          ListEmptyComponent={fetching ? <></> : <EmptyContent />}
          progressViewOffset={150}
        />

        <FloatingActionButton onPress={() => setShowCommentModal(true)} />
      </View>

      <BottomSheetModal
        isVisible={showCommentModal}
        onClose={() => setShowCommentModal(false)}
      >
        <CommentContent
          text={commonText}
          onNext={item => {
            setShowCommentModal(false);
            newTemplate(item);
          }}
          onDismiss={() => {
            setShowCommentModal(false);
          }}
        />
      </BottomSheetModal>

      <BottomSheetModal
        isVisible={showTemplateSuccess}
        onClose={() => setShowTemplateSuccess(false)}>
        <SuccessContent
          message="Your tally has been created"
          onDone={() => setShowTemplateSuccess(false)}
          onDismiss={() => setShowTemplateSuccess(false)}
        />
      </BottomSheetModal>

      <BottomSheetModal
        isVisible={showAcceptSuccess}
        onClose={() => setShowAcceptSuccess(false)}>
        <SuccessContent
          buttonTitle="View"
          message="Your tally is now open"
          onDone={onTallyOpenDone}
          onDismiss={() => setShowAcceptSuccess(false)}
        />
      </BottomSheetModal>

      <BottomSheetModal
        isVisible={showOfferSuccess.show}
        onClose={onDismissOfferSuccess}>
        <SuccessContent
          buttonTitle="View"
          message={`Sending tally offer to ${showOfferSuccess?.offerTo}`}
          onDone={onDoneOfferSuccess}
          onDismiss={onDismissOfferSuccess}
        />
      </BottomSheetModal>

      <BottomSheetModal
        isVisible={negotiationData.showModal}
        onClose={onNeogitationModalClose}>
        <TallyEntryModal
          shouldShowReview
          onNeogitationModalClose={onNeogitationModalClose}
          negotiationData={negotiationData}
          onReview={onReview}
          postOffer={postOffer}
          postAccept={postAccept}
        />
      </BottomSheetModal>
    </>
  );
};

const styles = StyleSheet.create({
  container: {
    flex: 1,
    backgroundColor: colors.white,
  },
  title: {
    fontSize: 16,
    color: colors.gray300,
    fontFamily: 'inter',
  },
  row: {
    flexDirection: 'row',
    justifyContent: 'space-between',
    alignItems: 'center',
  },
  contentContainerStyle: {
    marginTop: 20,
    backgroundColor: colors.white,
  },
  filterContainer: {
    borderWidth: 1,
    height: 30,
    borderColor: colors.white100,
    backgroundColor: colors.white200,
    flexDirection: 'row',
    borderRadius: 20,
    paddingHorizontal: 12,
    paddingVertical: 3,
    justifyContent: 'center',
    alignItems: 'center',
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
  rightActions: {
    width: 80,
    borderRadius: 2,
    alignItems: 'center',
    justifyContent: 'center',
  },
  row: {
    height: 60,
    marginRight: 18,
    flexDirection: 'row',
    justifyContent: 'flex-end',
  },
  itemView: {
    height: 70,
    marginHorizontal: 18,
    backgroundColor: colors.white,
    justifyContent: 'center',
    backgroundColor: colors.white,
  },
});

export default TallyInvite;
