import React, { useEffect, useState } from "react";
import { useDispatch, useSelector } from 'react-redux';
import {
  ScrollView,
  View,
  StyleSheet,
  RefreshControl,
  Keyboard,
  Platform,
  KeyboardAvoidingView,
  Text,
} from "react-native";

import { colors, toastVisibilityTime } from "../../../config/constants";
import useSocket from "../../../hooks/useSocket";
import useInvite from "../../../hooks/useInvite";
import { useTalliesMeText } from "../../../hooks/useLanguage";
import useTallyUpdate from "../../../hooks/useTallyUpdate";
import { fetchContracts, updateHoldCert } from "../../../services/tally";

import CustomText from "../../../components/CustomText";
import Button from "../../../components/Button";
import Spinner from "../../../components/Spinner";
import TallyEditView from "../TallyEditView";
import { Toast } from "react-native-toast-message/lib/src/Toast";
import { reviseTally } from "../../../services/tally";
import { UpdateHoldCert } from "./UpdateHoldCert";
import CenteredModal from "../../../components/CenteredModal";
import IconButton from "../../../components/IconButton";
import TickIcon from "../../../../assets/svg/tick.svg";
import CrossIcon from "../../../../assets/svg/cross.svg";
import { ShareIcon } from "../../../components/SvgAssets/SvgAssets";
import AcceptButton from '../AcceptButton';
import OfferButton from '../OfferButton';
import { fetchOpenTallies } from "../../../redux/openTalliesSlice";
import useMessageText from '../../../hooks/useMessageText';
import useTitle from '../../../hooks/useTitle';
import { showError } from "../../../utils/error";

const TallyPreview = (props) => {
  const dispatch = useDispatch()
  const { tally_seq, tally_ent } = props.route?.params ?? {};
  const { wm } = useSocket();
  const { setTriggerInviteFetch } = useInvite();
  const { certificateChangeTrigger } = useSelector(state => state.workingTallies);

  const [updating, setUpdating] = useState(false);
  const [tallyContracts, setTallyContracts] = useState([]);
  const [updateCert, setUpdateCert] = useState(false);

  const {
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
  } = useTallyUpdate(wm, tally_seq, tally_ent);

  useEffect(() => {
    fetchContracts(wm, {
      fields: ["top", "name", "title", "language", "host", "rid", "clean"],
      where: { top: true },
    }).then((data) => {
      setTallyContracts(data);
    });
  }, []);

  useEffect(() => {
    dispatch(fetchOpenTallies({ wm: wm }));

    const needCertUpdate = (
      tally_ent && tally_seq &&
      certificateChangeTrigger?.tally_ent == tally_ent && 
      certificateChangeTrigger?.tally_seq == tally_seq &&
      certificateChangeTrigger?.trigger &&
      certificateChangeTrigger?.hold_cert 
    )

    if(needCertUpdate) {
      setTally((prev) => {
        return {
          ...prev,
          hold_cert: certificateChangeTrigger.hold_cert,
        }
      });
    }
  }, [
    tally_ent,
    tally_seq,
    certificateChangeTrigger?.tally_ent,
    certificateChangeTrigger?.tally_seq,
    certificateChangeTrigger?.trigger,
    certificateChangeTrigger?.hold_cert,
  ])

  // Fetch tally text
  const talliesMeText = useTalliesMeText(wm)
  const talliesMeMessageText = talliesMeText?.msg ?? {};
  const { messageText } = useMessageText();
  const charkMessageText = messageText?.chark?.msg;

  useTitle(props.navigation, talliesMeMessageText?.detail?.title)

  const onDisplayCertUpdate = () => {
    setUpdateCert(true);
  };

  const onDismissCertUpdate = () => {
    setUpdateCert(false);
  };

  const onShare = () => {
    const hold_limit = tally?.hold_terms?.limit;
    const part_limit = tally?.part_terms?.limit;
    if (
      typeof hold_limit === "undefined" ||
      hold_limit === null ||
      typeof part_limit === "undefined" ||
      part_limit === null
    ) {
      return Toast.show({
        type: "error",
        text1: talliesMeMessageText?.noterms?.help,
        visibilityTime: toastVisibilityTime,
      });
    }

    return props.navigation.navigate("TallyShare", {
      tally_id: tally.tally_seq,
    });
  };

  const holdTermsData = Object.keys(holdTerms).reduce((acc, key) => {
    acc[key] = holdTerms[key] ? parseInt(holdTerms[key]) : undefined;
    return acc;
  }, {});

  const partTermsData = Object.keys(partTerms).reduce((acc, key) => {
    acc[key] = partTerms[key] ? parseInt(partTerms[key]) : undefined;
    return acc;
  }, {});

  // Update returns success but still not updating hold_cert
  const onUpdateCert = (cert) => {
    onDismissCertUpdate();
    updateHoldCert(wm, {
      hold_cert: cert,
      tally_ent,
      tally_seq,
    })
      .then((result) => {
        fetchTally();

        Toast.show({
          type: "success",
          text1: charkMessageText?.updated?.help ?? '',
          visibilityTime: toastVisibilityTime,
        });
      })
      .catch((err) => {
        showError(err);
      });
  };

  const onUpdate = () => {
    Keyboard.dismiss();

    setUpdating(true);

    const payload = {
      tally_type: tallyType,
      hold_terms: holdTermsData,
      part_terms: partTermsData,
      comment,
    };

    if (contract) {
      const found = tallyContracts?.find((item) => item.rid === contract);
      if (found) {
        payload.contract = {
          source: found.rid,
        };
      }
    }

    const spec = {
      fields: payload,
      view: "mychips.tallies_v_me",
      where: {
        tally_ent,
        tally_seq,
      },
    };

    wm.request("_tpt_ref" + Math.random(), "update", spec, (data, err) => {
      setUpdating(false);
      if (err) {
        return showError(err);
      }

      setTally(data);

      setInitialFields({
        ...initialFields,
        comment,
        holdLimit: holdTermsData?.limit,
        partLimit: partTermsData?.limit,
        contract: payload.contract?.source
          ? payload.contract.source
          : initialFields.contract,
      });

      Toast.show({
        type: "success",
        text1: charkMessageText?.updated?.help,
        visibilityTime: toastVisibilityTime,
      });

      setTriggerInviteFetch((c) => {
        return c + 1;
      });
    });
  };

  const onRevise = () => {
    reviseTally(wm, {
      tally_ent,
      tally_seq,
    }).then((data) => {
      setTally(data)
    }).catch((err) => {
      showError(err);
    });
  };

  const onViewContract = () => {
    props.navigation.navigate("TallyContract", { tally_seq });
  };

  const onCancel = () => {
    props.navigation.navigate("Invite");
  };

  const postOffer = () => {
    const partName = Object.values(tally.part_cert?.name ?? {}).join(" ");
    props.navigation.navigate("Invite", {
      fromOffer: {
        show: true,
        offerTo: partName,
        tally_ent: tally?.tally_ent,
        tally_seq: tally?.tally_seq,
      },
    });
  }

  const postAccept = () => {
    Toast.show({
      type: "success",
      text1: talliesMeMessageText?.accepted?.title ?? '',
      visibilityTime: toastVisibilityTime,
    });
    props.navigation.goBack();
  }

  const isDirty =
    initialFields.tallyType !== tallyType ||
    initialFields.comment !== comment ||
    initialFields.contract !== contract ||
    initialFields.holdLimit != holdTerms?.limit ||
    initialFields.partLimit != partTerms?.limit;


  if (loading) {
    return (
      <View style={{ flex: 1, alignItems: "center", justifyContent: "center" }}>
        <Spinner text="Loading..." />
      </View>
    );
  }

  if (!tally) {
    return (
      <View style={{ flex: 1, alignItems: "center" }}>
        <CustomText as="h2">Tally not found</CustomText>
      </View>
    );
  }

  const state = tally.state;
  const canShare = state === "draft";
  const canOffer = state === "P.draft";
  const canAccept = state === "P.offer";
  //const canRefuse = hasPartCert && state === 'offer';

  const action = () => {
    if (isDirty && state !== "H.offer") {
      return (
        <View style={styles.changedAction}>
          <IconButton style={styles.actionButton('#D95656')} onPress={onCancel}>
            <CrossIcon width={50} height={50} />
          </IconButton>

          <IconButton
            style={styles.actionButton('#155CEF')}
            onPress={onUpdate}
            disabled={updating}
          >
            <View style={styles.tickButton}>
            <TickIcon width={50} height={50} />
            </View>
          </IconButton>
        </View>
      );
    }

    if (canShare) {
      return (
        <View style={styles.changedAction}>
          <IconButton style={styles.actionButton('#D95656')} onPress={onCancel}>
            <CrossIcon width={50} height={50} />
          </IconButton>

          <IconButton style={styles.actionButton(colors.blue)} onPress={onShare}>
            <ShareIcon size={30} color={colors.white} useNativeIcon={true} />
          </IconButton>
        </View>
      );
    }

    if (canOffer) {
      return (
        <>
          <OfferButton
            text={{ offer: talliesMeMessageText?.offer }}
            tally={tally}
            postOffer={postOffer}
            style={styles.fullActionButton(colors.yellow)}
          />
        </>
      );
    }

    if (canAccept) {
      return (
        <View style={styles.buttonWrapper}>
          <Button
            title={talliesMeMessageText?.revise?.title ?? 'revise_text'}
            onPress={onRevise}
            textColor={colors.white}
            style={[styles.fullActionButton(colors.yellow), { width: '48%' }]}
          />

          <AcceptButton
            text={{ accept: talliesMeMessageText?.accept }}
            tally={tally}
            postAccept={postAccept}
            style={[styles.fullActionButton(colors.blue), { width: '48%' }]}
          />
        </View>
      )
    }

    return null;
  };

  return (
    <>
      <KeyboardAvoidingView
        style={[styles.container]}
        behavior={Platform.OS === "ios" ? "padding" : undefined}
        keyboardVerticalOffset={Platform.OS === "ios" ? 100 : 0}
      >

        <ScrollView
          style={styles.scrollView}
          contentContainerStyle={styles.contentContainer}
          keyboardShouldPersistTaps="handled"
          refreshControl={
            <RefreshControl refreshing={refreshing} onRefresh={fetchTally} />
          }
        >
          <TallyEditView
            tally={tally}
            tallyType={tallyType}
            contract={contract}
            holdTerms={holdTerms}
            partTerms={partTerms}
            comment={comment}
            setComment={setComment}
            onHoldTermsChange={onHoldTermsChange}
            onPartTermsChange={onPartTermsChange}
            setTallyType={setTallyType}
            setContract={setContract}
            onViewContract={onViewContract}
            tallyContracts={tallyContracts}
            navigation={props.navigation}
            onUpdateContract={() => {
              onDisplayCertUpdate();
            }}
          />
        </ScrollView>

        <View style={styles.actions}>{action()}</View>

        {updating && (
          <View style={{ position: "absolute", bottom: 25, left: "35%" }}>
            <Text
              style={{
                borderRadius: 10,
                paddingHorizontal: 15,
                paddingVertical: 5,
                color: colors.black,
                borderColor: colors.gray5,
                borderWidth: 1,
              }}
            >
              Updating...
            </Text>
          </View>
        )}
      </KeyboardAvoidingView>

      <CenteredModal isVisible={updateCert} onClose={onDismissCertUpdate}>
        <UpdateHoldCert
          onUpdateCert={onUpdateCert}
          onDismiss={onDismissCertUpdate}
          tallyCurrentHoldCert={tally?.hold_cert}
        />
      </CenteredModal>
    </>
  );
};

const styles = StyleSheet.create({
  container: {
    flex: 1,
    paddingBottom: 15,
  },
  scrollView: {
    paddingBottom: 15,
    marginBottom: 55,
  },
  contentContainer: {
    backgroundColor: "white",
    margin: 10,
    padding: 10,
    paddingBottom: 20,
  },
  toolbar: {
    flexDirection: "row",
    padding: 16,
    height: 56,
    alignItems: "center",
    backgroundColor: "white",
    elevation: 8,
  },
  detailControl: {
    marginVertical: 10,
  },
  input: {
    paddingHorizontal: 10,
    paddingVertical: 10,
    backgroundColor: colors.gray100,
  },
  comment: {
    textAlignVertical: "top",
  },
  headerText: {
    color: colors.black,
    fontSize: 14,
  },
  shareButton: {
    marginLeft: 10,
    borderColor: colors.quicksilver,
    backgroundColor: colors.quicksilver,
  },
  refuse: {
    backgroundColor: colors.orangeRed,
    borderColor: colors.orangeRed,
    marginLeft: 10,
  },
  actions: {
    marginHorizontal: 10,
    paddingHorizontal: 10,
  },
  changedAction: {
    left: 0,
    right: 0,
    bottom: 5,
    padding: 10,
    paddingVertical: 20,
    position: "absolute",
    flexDirection: "row",
    justifyContent: "space-between",
  },
  actionButton:(color)=> ({
    width: 55,
    height: 55,
    elevation: 2,
    shadowColor: colors.black,
    shadowOffset: {
      height: 1,
      width: 1,
    },
    shadowOpacity: 0.5,
    backgroundColor: color,
    alignItems: "center",
    borderRadius: 35,
    justifyContent: "center",
  }),
  tickButton:{backgroundColor:colors.white,height:30,width:30,justifyContent:'center',alignItems:'center'},
  fullActionButton: (backgroundColor) => ({
    marginBottom: 5,
    backgroundColor,
    borderColor: backgroundColor,
    borderRadius: 18,
    height: 45,
    justifyContent: "center",
  }),
  buttonWrapper:{ flexDirection: 'row', justifyContent: 'space-between', position: 'absolute', bottom: 5, right:20, left:20 }
});

export default TallyPreview;
