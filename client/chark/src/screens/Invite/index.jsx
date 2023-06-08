import React, { useState, useEffect } from 'react';
import { View, FlatList, Text, StyleSheet, ActivityIndicator, ScrollView, Modal } from 'react-native';
import Toast from 'react-native-toast-message';

import { colors } from '../../config/constants';
import { random } from '../../utils/common';
import useSocket from '../../hooks/useSocket';
import useInvite from '../../hooks/useInvite';
import { createTemplate } from '../../services/tally';

import TemplateItem from './TemplateItem';
import Button from '../../components/Button';

const TallyInvite = (props) => {
  const [data, setData] = useState([]);
  const [loading, setLoading] = useState(false);
  const { wm, ws } = useSocket();
  const { triggerInviteFetch } = useInvite();

  useEffect(() => {
    if (ws) {
      fetchTemplates();
    }
  }, [ws, triggerInviteFetch]);

  //Create a new template
  const newTemplate = () => {
    const payload = {
      contract: { terms: 'Some Terms' },
      comment: 'Test: ' + new Date(),
      hold_terms: {
        call: 30,
      }, part_terms: {
        call: 30,
      },
    }

    createTemplate(wm, payload).then(() => {
      fetchTemplates()
    }).catch(err => {
      Toast.show({
        type: 'error',
        text1: err?.message ?? 'Error creating new template',
      });
    })
  }

  const fetchTemplates = () => {
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
      ],
      view: 'mychips.tallies_v_me',
      where: { left: "status", oper: "in", entry: "draft offer" },
      order: {
        field: 'crt_date',
        asc: false,
      }
    }

    wm.request('_inv_ref' + random(), 'select', spec, (data, err) => {
      const _data = data?.map(el => ({
        tally_ent: el.tally_ent,
        id: el.tally_seq,
        contract: el.contract,
        comment: el.comment,
        hold_terms: el.hold_terms,
        part_terms: el.part_terms,
        tally_type: el.tally_type,
        status: el.status,
        part_cid: el.part_cid,
      }));

      setData(_data);
      setLoading(false);
    });
  }

  const renderItem = ({ item, index }) => {
    return (
      <TemplateItem
        testID={`tally-${index}`}
        template={item}
        navigation={props.navigation}
      />
    )
  }

  return (
    <View style={styles.container} testID="inviteScreen">
      <View
        style={styles.listContainer}
      >
        <View
          style={styles.listHeading}
        >
          <Text style={styles.templateText}>Drafts: </Text>

          <View style={{ marginLeft: 10 }}>
            <Button
              title="New Draft"
              onPress={() => newTemplate()}
            />
          </View>
        </View>

        <FlatList
          data={data}
          renderItem={renderItem}
          refreshing={loading}
          onRefresh={() => fetchTemplates()}
        />

      </View>
    </View>
  )
}

const styles = StyleSheet.create({
  container: {
    flex: 1,
    margin: 10,
    padding: 10,
    backgroundColor: colors.white,
  },
  listContainer: {
    flex: 1,
  },
  listHeading: {
    flexDirection: 'row',
    flexWrap: 'wrap',
    marginVertical: 10,
    alignItems: 'center',
  },
  webViewContainer: {
    flex: 1,
  },
  templateText: {
    marginVertical: 10,
    fontSize: 18,
    fontWeight: 'bold',
    color: colors.black,
  },
  regenerate: {
    marginBottom: 10,
  },
})

export default TallyInvite;
