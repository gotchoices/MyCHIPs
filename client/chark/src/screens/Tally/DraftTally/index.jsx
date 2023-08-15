import React, { useEffect, useState } from "react"
import { ActivityIndicator, FlatList, StyleSheet, View } from "react-native"
import useSocket from "../../../hooks/useSocket";
import TemplateItem from "../../Invite/TemplateItem";
import { random } from "../../../utils/common";
import { colors } from "../../../config/constants";
import Button from "../../../components/Button";
import CenteredModal from "../../../components/CenteredModal";
import { UpdateHoldCert } from "../TallyPreview/UpdateHoldCert";
import { Toast } from "react-native-toast-message/lib/src/Toast";

const DraftTally = (props) => {
  const tallyProcess = props.route?.params ?? {};
  const [loading, setLoading] = useState(false);
  const [updateCertVisible, setUpdateCertVisible] = useState(false);
  const [data, setData] = useState([]);
  const { wm } = useSocket();

  useEffect(() => {
    if (wm) {
      fetchDraftTallies();
    }
  }, [wm]);

  const fetchDraftTallies = () => {
    setLoading(true);
    const spec = {
      fields: [
        'tally_ent',
        'tally_seq',
        'contract',
        'comment',
        'tally_uuid',
        'hold_terms',
        'part_terms',
        'tally_type',
        'status',
        'part_cid',
        'part_cert',
        'hold_cert',
      ],
      view: 'mychips.tallies_v_me',
      where: { left: "status", oper: "in", entry: ['draft'] },
      order: {
        field: 'crt_date',
        asc: false,
      }
    }

    wm.request('_inv_ref' + random(), 'select', spec, (data, err) => {
      const _data = data;
      setData(_data);
      setLoading(false);
    });
  }

  const onShowUpdateCert = () => {
    setUpdateCertVisible(true);
  }

  const onDismissUpdateCert = () => {
    setUpdateCertVisible(false);
  }

  const startProcessingTally = (partCert) => {
    console.log("PART_CERT ==> ", JSON.stringify(partCert));
    const spec = {
      view: 'mychips.ticket_process',
      params: [{ ...tallyProcess, part_cert: partCert }],
    }

    Toast.show({
      type: 'info',
      text1: 'Processing tally ticket...',
    });

    wm.request('_process_tally', 'select', spec, (data, err) => {
      if (err) {
        Toast.show({
          type: 'error',
          text1: err.message ?? 'Error processing tally ticket.',
        })
      } else if (data?.[0]?.ticket_process) {
        Toast.show({
          type: 'success',
          text1: 'Tally ticket processed.'
        });
        props.navigation.goBack();
      } else {
        Toast.show({
          type: 'error',
          text1: 'Tally ticket process failed.'
        })
      }
    });
  }

  const renderItem = ({ item, index }) => {
    return (
      <TemplateItem
        testID={`tally-${index}`}
        template={item}
        navigation={props.navigation}
        onItemSelected={item => {
          startProcessingTally(item.hold_cert);
        }}
      />
    )
  }
  if (loading) {
    return <View style={[styles.container, { justifyContent: 'center', alignItems: 'center' }]}>
      <ActivityIndicator />
    </View>
  }

  const HeaderContent = () => {
    return <View style={{ paddingBottom: 16, justifyContent: 'center', alignItems: 'flex-end' }}>
      <Button
        title="Customize"
        onPress={onShowUpdateCert}
      />
    </View>
  }

  return <>
    <View style={styles.container}>
      <FlatList
        contentContainerStyle={styles.contentContainer}
        ListHeaderComponent={<HeaderContent />}
        data={data}
        keyExtractor={(item, index) => `${item?.tally_uuid}${index}`}
        ItemSeparatorComponent={() => <View style={{ height: 16 }} />}
        renderItem={renderItem}
      />
    </View>
    <CenteredModal
      isVisible={updateCertVisible}
      onClose={onDismissUpdateCert}
    >
      <UpdateHoldCert
        onDismiss={onDismissUpdateCert}
        onUpdateCert={(data) => {
          onDismissUpdateCert();
          startProcessingTally(data);
        }}
      />
    </CenteredModal>
  </>
}

const styles = StyleSheet.create({
  container: {
    flex: 1,
  },
  contentContainer: {
    padding: 16,
    backgroundColor: colors.white
  }
})

export default DraftTally;