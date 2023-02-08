import React, { useState, useEffect } from 'react';
import { WebView } from 'react-native-webview';
import { View, FlatList, Text, StyleSheet, ActivityIndicator, ScrollView, Modal } from 'react-native';

import { colors } from '../../config/constants';
import { request } from '../../services/profile';
import { random } from '../../utils/common';
import useSocket from '../../hooks/useSocket';

import TemplateItem from './TemplateItem';
import ShareTally from './ShareTally';
import CenteredModal from '../../components/CenteredModal';
import Button from '../../components/Button';

const TallyInvite = (props) => {
  const [data, setData] = useState([]);
  const [loading, setLoading] = useState(false);
  const [selectedTallySeq, setSelectedTallySeq] = useState();
  const [tallyShareInfo, setTallyShareInfo] = useState();
  const [isVisible, setIsVisible] = useState(false);
  const [generatingInvite, setGeneratingInvite] = useState(false);
  const { wm, ws } = useSocket();

  useEffect(() => {
    fetchTemplates();
  }, [ws]);

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

    wm.request('_tpt_ref', 'insert', spec, data => {
console.log('Insert done')
      fetchTemplates()
    });
  }

  const fetchTemplates = () => {
    setLoading(true);
    setSelectedTallySeq(undefined);
    const spec = {
      fields: ['tally_ent', 'tally_seq', 'contract', 'comment', 'tally_uuid'],
      view: 'mychips.tallies_v_me',
      where: { status: 'draft' }
    }

    wm.request('_inv_ref', 'select', spec, data => {
      const _data = data?.map(el => ({ tally_ent: el.tally_ent, id: el.tally_seq, contract: el.contract, comment: el.comment }))
      setData(_data);
      setLoading(false);
      setTallyShareInfo(undefined)
    });
  }

  const generate = () => {
    if(!selectedTallySeq) {
      return;
    }

    setGeneratingInvite(true);
    const template = data?.find((item) => item.id === selectedTallySeq); 

    const spec = {
      name: 'invite',
      view: 'mychips.tallies_v_me',
      data: {
        keys: [{tally_seq: template.id}],
        options: {
          reuse: true, format: 'json'
        }
      }
    }

    const qrSpec = {
      name: 'invite',
      view: 'mychips.tallies_v_me',
      data: {
        keys: [{tally_seq: template.id}],
        options: {
          reuse: true, format: 'qr'
        }
      }
    }

    const linkSpec = {
      name: 'invite',
      view: 'mychips.tallies_v_me',
      data: {
        keys: [{tally_seq: template.id}],
        options: {
          reuse: true, format: 'link'
        }
      }
    }

    request(wm, `_invite_ref_json_${random(1000)}`, 'action', spec).then((data) => {
      setGeneratingInvite(false);
      setTallyShareInfo({
        json: data,
      });
      setIsVisible(true)
    });
  }

  const onShareClose = () => {
    setTallyShareInfo(undefined);
    setSelectedTallySeq(undefined);
    setIsVisible(false)
  }

  const renderItem = ({ item }) => {
    return (
      <TemplateItem 
        template={item}
        activeId={selectedTallySeq}
        selectTemplate={selectTemplate}
        navigation={props.navigation}
      />
    )
  }

  if(tallyShareInfo) {
    return <View style={styles.container}>
      <ShareTally
        tally={tallyShareInfo?.json ?? {}}
        onCancel={onShareClose}
      />
    </View>
  }

  return (
    <View style={styles.container}>
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
            <View style={{ marginLeft: 10 }}>
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

      <CenteredModal
        isVisible={isVisible}
        onClose={onShareClose}
      >
        {
          tallyShareInfo?.qrCode  && (
            <ShareTally
              qrCode={tallyShareInfo?.qrCode ?? ''}
              link={tallyShareInfo?.link ?? ''}
              onCancel={onShareClose}
            />
          )
        }
      </CenteredModal>
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
