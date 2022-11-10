import React, { useState, useEffect } from 'react';
import { WebView } from 'react-native-webview';
import { View, Button, FlatList, Text, StyleSheet, ActivityIndicator } from 'react-native';

import TemplateItem from './TemplateItem';

const TallyInvite = (props) => {
  const wm = props.wm;
  const [data, setData] = useState([]);
  const [loading, setLoading] = useState(false);
  const [selectedTallySeq, setSelectedTallySeq] = useState();

  useEffect(() => {
    fetchTemplates();
  }, []);

  const selectTemplate = (tally_seq) => {
    setSelectedTallySeq(tally_seq);
  }

  //Re-load templates from DB
  const fetchTemplates = () => {
    setLoading(true);
    setSelectedTallySeq(undefined);
    const spec = {
      fields: ['tally_seq', 'contract', 'comment'],
      view: 'mychips.tallies_v_me',
      where: {status: 'draft'}
    }

    wm.request('_inv_ref', 'select', spec, data => {
      const _data = data.map(el => ({ id: el.tally_seq, contract: el.contract, comment: el.comment }))
      setData(_data);
      setLoading(false);
    });
  }

  const generate = () => {
    if(!selectedTallySeq) {
      return;
    }

    const template = data?.find((item) => item.id === selectedTallySeq); 
    console.log(template, 'template')
    return;

    wm.request('_invite', 'action', {name:'invite', view:'mychips.tallies_v'}, data => {
      console.log('TI data:', data)
    })
  }

  const renderItem = ({ item }) => {
    return (
      <TemplateItem 
        template={item}
        activeId={selectedTallySeq}
        selectTemplate={selectTemplate}
      />
    )
  }

  return (
    <View style={styles.container}>
      <WebView
        source={{ uri: 'http://gotchoices.org' }}
        style={styles.webView}
      />

      <Text style={styles.templateText}>Templates:</Text>

      <FlatList 
        data={data}
        renderItem={renderItem}
      />

      {
        selectedTallySeq && (
          <View style={styles.regenerate}>
            <Button
              title="Regenerate"
              onPress={() => generate()}
            />
          </View>
        )
      }
      <Button
        title="Refresh"
        onPress={() => fetchTemplates()}
      />
    </View>
  )
}

const styles = StyleSheet.create({
  container: {
    height: 400,
  },
  webView: {
    maxHeight: 360,
    width: 300
  },
  templateText: {
    marginVertical: 10,
  },
  regenerate: {
    marginBottom: 10,
  },
})

export default TallyInvite;
