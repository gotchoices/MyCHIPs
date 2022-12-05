import React, { useState, useEffect } from 'react';
import { WebView } from 'react-native-webview';
import { View, Button, FlatList, Text, StyleSheet, ActivityIndicator, ScrollView } from 'react-native';

import TemplateItem from './TemplateItem';

const TallyInvite = (props) => {
  const wm = props.wm;
  const [data, setData] = useState([]);
  const [loading, setLoading] = useState(false);
  const [selectedTallySeq, setSelectedTallySeq] = useState();
  const [qrCode, setQrCode] = useState();

  useEffect(() => {
    fetchTemplates();
  }, []);

  const selectTemplate = (tally_seq) => {
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
      setQrCode(undefined);
    });
  }

  const generate = () => {
    if(!selectedTallySeq) {
      return;
    }

    const template = data?.find((item) => item.id === selectedTallySeq); 

    let control = {
      name: 'invite',
      view: 'mychips.tallies_v_me',
      data: {
        keys: [{tally_seq: template.id}],
        options: {reuse: true}
      }
    }

    wm.request('_invite', 'action', control, data => {
      setQrCode(data);
      console.log('TI data:', data)
    })
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

  return (
    <View style={styles.container}>
      {
        qrCode && (
          <View style={styles.webViewContainer}>
            <WebView
              originWhitelist={['*']}
              source={{ html: qrCode }}
            />
          </View>
        )
      }

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
                color="#ce8805"
                title="From Template"
                onPress={() => generate()}
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
    marginTop: 20,
  },
  listContainer: {
    paddingVertical: 10,
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
  },
  regenerate: {
    marginBottom: 10,
  },
})

export default TallyInvite;
