import {
  View,
  Text,
  ScrollView,
  StyleSheet,
  RefreshControl,
} from "react-native";
import React, { useEffect, useState, useMemo } from "react";
import { useSelector, useDispatch } from "react-redux";

import {
  fetchTallies,
  fetchContracts,
} from "../../../services/tally";
import useSocket from "../../../hooks/useSocket";
import { colors } from "../../../config/constants";
import { useTalliesMeText } from "../../../hooks/useLanguage";
import useTitle from '../../../hooks/useTitle';
import { updateValidity } from "../../../redux/updateTallySlice";
import { repairTallySignature, repairTallyCertificate } from "../../../utils/tally-repair";

import CustomText from "../../../components/CustomText";
import TallyEditView from '../TallyEditView';

const EditOpenTally = (props) => {
  const { tally_seq, tally_ent } = props.route?.params ?? {};
  const { wm } = useSocket();
  const dispatch = useDispatch();
  
  // Get validation status from Redux
  const validityStatuses = useSelector(state => state.updateTally.validityStatuses || {});

  const [loading, setLoading] = useState(true);
  const [tally, setTally] = useState();
  const [tallyContracts, setTallyContracts] = useState([]);

  const talliesMeText = useTalliesMeText(wm);
  const talliesMeMsgText = talliesMeText?.msg;
  const statusValues = talliesMeText?.col?.status?.values;
  const openText = useMemo(() => {
    return statusValues?.find(s => s.value === 'open');
  }, [statusValues])

  useTitle(props.navigation, openText ? `${talliesMeMsgText?.detail?.title ?? ''} - ${openText?.title ?? ''} `: null)

  // fields: ['tally_uuid', 'tally_date', 'status', 'target', 'bound', 'reward', 'clutch', 'part_cert'],
  useEffect(() => {
    fetchTally();
  }, [tally_seq, tally_ent]);


  const fetchTally = () => {
    setLoading(true);
    fetchTallies(wm, {
      fields: [
        "bound",
        "reward",
        "clutch",
        "tally_seq",
        "tally_uuid",
        "tally_date",
        "status",
        "hold_terms",
        "part_terms",
        "part_cert",
        "tally_type",
        "comment",
        "contract",
        "net",
        'hold_cert',
        'hold_chad',
        'hold_sig',   // Added for signature display
        'part_sig',   // Added for signature display
        'json_core',  // Needed for validation
      ],
      where: {
        tally_ent,
        tally_seq,
      },
    })
      .then((data) => {
        if (data?.length) {
          const _tally = data?.[0];
          setTally(_tally);
          
          // Update validity status in Redux if needed
          if (_tally?.tally_uuid) {
            dispatch(updateValidity(_tally));
          }
        }
      })
      .catch((e) => {
        console.log("ERROR===>", e);
      })
      .finally(() => {
        setLoading(false);
      });
  };

  useEffect(() => {
    fetchContracts(wm, {
      fields: ["top", "name", "title", "language", "host", "rid", "clean"],
      where: { top: true },
    }).then((data) => {
      setTallyContracts(data);
    });
  }, []);

  const onViewContract = () => {
    props.navigation.navigate("TallyContract", { tally_seq });
  };
  
  // Function to re-sign the tally with the current key
  const handleReSign = () => {
    if (tally && tally.tally_seq) {
      repairTallySignature(wm, tally.tally_seq);
    }
  };
  
  // Function to update holder certificate with current key
  const handleUpdateCert = () => {
    if (tally && tally.tally_seq) {
      repairTallyCertificate(wm, tally.tally_seq);
    }
  };

  if (loading) {
    return (
      <View style={{ flex: 1, alignItems: "center", justifyContent: "center" }}>
        <Text>Loading...</Text>
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

  const holdTerms = {
    limit: tally.hold_terms?.limit?.toString(),
    call: tally.hold_terms?.call?.toString(),
  };

  const partTerms = {
    limit: tally.part_terms?.limit?.toString(),
    call: tally.part_terms?.call?.toString(),
  };

  // Get the tally's validity status from Redux
  const tallyValidityStatus = tally?.tally_uuid ? validityStatuses[tally.tally_uuid] : undefined;

  return (
    <View style={{ flex: 1 }}>
      <ScrollView
        style={styles.scrollView}
        contentContainerStyle={styles.contentContainer}
        keyboardShouldPersistTaps="handled"
        refreshControl={
          <RefreshControl refreshing={loading} onRefresh={fetchTally} />
        }
      >
        <TallyEditView
          tally={tally}
          tallyType={tally.tally_type}
          contract={tally.contract?.source ?? ''}
          holdTerms={holdTerms}
          partTerms={partTerms}
          comment={tally.comment ?? ''}
          onViewContract={onViewContract}
          tallyContracts={tallyContracts}
          navigation={props.navigation}
          onReSign={handleReSign}
          onUpdateCert={handleUpdateCert}
        />
      </ScrollView>
    </View>
  );
};

const styles = StyleSheet.create({
  container: {
    margin: 10,
    padding: 10,
    marginVertical:5,
    backgroundColor: colors.white,
  },
  contentContainer: {
    backgroundColor: "white",
    margin: 10,
    padding: 10,
    paddingBottom: 20,
  },
  scrollView: {
    paddingBottom: 15,
    marginBottom: 55,
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
  textInputStyle: {
    marginTop:5,
    fontSize: 12,
    color: "black",
    paddingVertical: 16,
    paddingHorizontal: 10,
    backgroundColor: colors.gray100,
  },
  label: {
    fontWeight: "500",
    fontSize: 13,
    marginBottom: 0,
    color: colors.black,
  },
  headerText: {
    fontSize: 14,
    color: 'black',
  },
  showPDF: {
    marginTop: 12,
    backgroundColor: colors.white
  ,
  h5: {
    fontSize: 12,
    marginBottom: 0,
    fontWeight: "500",
    color: colors.gray300,
  },}

})

export default EditOpenTally;
