import React, { useState, useEffect } from 'react';
import { View, FlatList, Text, StyleSheet, ActivityIndicator, ScrollView, Modal } from 'react-native';
import Toast from 'react-native-toast-message';

import { colors } from '../../config/constants';
import { request } from '../../services/profile';
import { random } from '../../utils/common';
import useSocket from '../../hooks/useSocket';
import useInvite from '../../hooks/useInvite';

import TemplateItem from './TemplateItem';
import ShareTally from './ShareTally';
import CenteredModal from '../../components/CenteredModal';
import Button from '../../components/Button';

const TallyInvite = (props) => {
  const [data, setData] = useState([]);
  const [loading, setLoading] = useState(false);
  const [selectedTallySeq, setSelectedTallySeq] = useState();
  const [tallyShareInfo, setTallyShareInfo] = useState();
  const [generatingInvite, setGeneratingInvite] = useState(false);
  const { wm, ws } = useSocket();
  const { triggerInviteFetch } = useInvite();

  useEffect(() => {
    if(ws) {
      fetchTemplates();
    }
  }, [ws, triggerInviteFetch]);

  const selectTemplate = (tally_seq) => {
    if(tally_seq === selectedTallySeq) {
      setSelectedTallySeq(undefined);
      setTallyShareInfo(undefined)
      return;
    }
    setSelectedTallySeq(tally_seq);
  }

  //Create a new template
  const newTemplate = () => {
    const spec = {
      fields: {
        contract: {terms: 'Some Terms'},
        comment: 'Test: ' + new Date()
      },
      view: 'mychips.tallies_v_me',
    }

    wm.request('_tpt_ref' + random(), 'insert', spec, () => {
      fetchTemplates()
    });
  }

  const fetchTemplates = () => {
    setLoading(true);
    setSelectedTallySeq(undefined);
    const spec = {
      fields: ['tally_ent', 'tally_seq', 'contract', 'comment', 'tally_uuid', 'hold_terms', 'part_terms'],
      view: 'mychips.tallies_v_me',
      where: { state: 'draft' },
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
      }));

      setData(_data);
      setLoading(false);
      setTallyShareInfo(undefined)
    });
  }

  const generate = () => {
    if(!selectedTallySeq) {
      return;
    }

    const template = data?.find((item) => item.id === selectedTallySeq); 

    const hold_limit = template?.hold_terms?.limit;
    const part_limit = template?.part_terms?.limit;
    if(
      typeof hold_limit === 'undefined' || hold_limit === null ||
      typeof part_limit === 'undefined' || part_limit === null
    ) {
      return Toast.show({
        type: 'error',
        text1: 'Please add hold terms and part terms before sharing tally.',
      });
    }

    setGeneratingInvite(true);
    const spec = {
      name: 'invite',
      view: 'mychips.tallies_v_me',
      data: {
        keys: [{tally_seq: template.id}],
        options: {
          reuse: true,
          format: ['json', 'link']
        }
      }
    }

    request(wm, `_invite_ref_json_${random(1000)}`, 'action', spec).then((data) => {
      const json = data?.[0];
      const link = data?.[1];

      setGeneratingInvite(false);
      setTallyShareInfo({
        json,
        link,
      });
    });
  }

  const onShareClose = () => {
    setTallyShareInfo(undefined);
    setSelectedTallySeq(undefined);
  }

  const renderItem = ({ item, index }) => {
    return (
      <TemplateItem 
        testID={`tally-${index}`}
        template={item}
        activeId={selectedTallySeq}
        selectTemplate={selectTemplate}
        navigation={props.navigation}
      />
    )
  }

  if(tallyShareInfo) {
    return <View style={styles.container} testID="tallyShare">
      <ShareTally
        json={tallyShareInfo?.json ?? {}}
        link={tallyShareInfo?.link ?? ''}
        onCancel={onShareClose}
      />
    </View>
  }

  return (
    <View style={styles.container} testID="inviteScreen">
      <View 
        style={styles.listContainer}
      >
        <View
          style={styles.listHeading}
        >
          <Text style={styles.templateText}>Templates: </Text>

          <View style={{ marginLeft: 10 }}>
            <Button
              title="New Invite"
              onPress={() => newTemplate()}
            />
          </View>

        {
          selectedTallySeq && (
            <View style={{ marginLeft: 10 }} testID="templateBtn">
              <Button
                style={{ backgroundColor: colors.mustardBrown, borderColor: colors.mustardBrown }}
                title="From Template"
                onPress={() => generate()}
                disabled={generatingInvite}
              />
            </View>
          )
        }
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
