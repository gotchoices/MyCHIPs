import React, { useEffect } from 'react';
import { View, Text, StyleSheet, ScrollView } from 'react-native';

import ActiveKey from './ActiveKey';
import GenerateKey from './GenerateKey';
import ImportKey from './ImportKey';
import Export from './Export';

import { colors } from '../../config/constants';
import useMessageText from '../../hooks/useMessageText';

const KeyManagement = (props) => {
  const { messageText } = useMessageText();
  const charkText = messageText?.chark?.msg;

  const commonText = {
    public: charkText?.public,
    private: charkText?.private,
    keywarn: charkText?.keywarn,
    import: charkText?.import,
    export: charkText?.export,
    nokey: charkText?.nokey,
    biofail: charkText?.biofail,
    keybio: charkText?.keybio,
    keypass: charkText?.keypass,
    keygen: charkText?.keygen,
    success: charkText?.success,
  };

  useEffect(() => {
    if(charkText?.keys?.title) {
      props.navigation.setOptions({ title: charkText?.keys?.title })
    }
  }, [charkText?.keys?.title])
  
  // Extract params from navigation props to pass to ImportKey
  const signkeyUrl = props.route?.params?.signkeyUrl;
  
  // Setting autoImport to true when signkeyUrl is provided, unless explicitly set to false
  const autoImport = props.route?.params?.autoImport !== false 
    ? (props.route?.params?.autoImport || Boolean(signkeyUrl)) 
    : false;
    
  const jsonData = props.route?.params?.jsonData;

  return (
    <ScrollView
      style={styles.container}
      contentContainerStyle={styles.contentContainer}
    >
      <View style={{ marginBottom: 30 }}>
        <Text style={styles.description}>
          {charkText?.keys?.help ?? ''}
        </Text>
      </View>

      <ActiveKey text={commonText} />

      <GenerateKey text={commonText} />

      <ImportKey 
        navigation={props.navigation} 
        route={props.route}
        text={commonText}
        signkeyUrl={signkeyUrl}
        autoImport={autoImport || Boolean(signkeyUrl)}
        jsonData={jsonData}
      />

      <Export text={commonText} />
    
    </ScrollView>
  )
}

const styles = StyleSheet.create({
  container: {
    flex: 1,
  },
  contentContainer: {
    padding: 20,
  },
  description: {
    fontFamily: 'inter',
    fontWeight: '500',
    textAlign: 'center',
    color: colors.black,
    fontSize: 13,
    lineHeight: 18,
  },
});

export default KeyManagement;
