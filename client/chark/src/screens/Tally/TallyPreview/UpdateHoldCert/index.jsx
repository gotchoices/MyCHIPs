import React, { useCallback, useEffect, useState } from "react"
import { ScrollView, StyleSheet, Text, View } from "react-native"
import { useSelector } from 'react-redux';

import { colors } from "../../../../config/constants";
import Button from "../../../../components/Button";
import CheckBox from "@react-native-community/checkbox";
import useProfile from "../../../../hooks/useProfile";
import { useUser } from "../../../../hooks/useLanguage";
import useMessageText from "../../../../hooks/useMessageText";
import useSocket from "../../../../hooks/useSocket";
import HelpText from "../../../../components/HelpText";

export const UpdateHoldCert = ({ onDismiss, onUpdateCert, tallyCurrentHoldCert }) => {
  // tallyCurrentHoldCert is certificate that user has selected for tally
  // User currenct certificate
  const { wm } = useSocket();
  const { personal } = useSelector(state => state.profile);
  const [tallyCert, setTallyCert] = useState({ ...tallyCurrentHoldCert ?? {} });
  const [userCert, setUserCert] = useState({});

  useUser(wm);
  const { messageText } = useMessageText();
  const certificateLang = messageText?.users?.cert?.values;


  useEffect(() => {
    const cert = personal?.cert;
    if (cert) {
      setTallyCert(recentCert => {
        return {
          ...recentCert,
          chad: recentCert?.chad ?? cert?.chad,
          date: recentCert?.date ?? cert?.date,
          name: recentCert?.name ?? cert?.name,
          public: recentCert?.public ?? cert?.public,
          type: recentCert?.type ?? cert?.type,
        }
      });
      setUserCert(cert);
    }
  }, [personal])

  const onUpdate = () => {
    onUpdateCert(tallyCert);
  }

  const isMandatory = (key) => {
    if (key === 'chad' || key === 'date' || key === 'name' || key === 'public' || key === 'type') {
      return true;
    } else {
      return false;
    }
  }

  const onRestoreCert = () => {
    // const cert = personal?.cert;
    setTallyCert({ ...userCert });

    return;
    setTallyCert(recentCert => {
      return {
        ...tallyCurrentHoldCert,
        chad: recentCert?.chad ?? cert?.chad,
        date: recentCert?.date ?? cert?.date,
        name: recentCert?.nam ?? cert?.name,
        public: recentCert?.public ?? cert?.public,
        type: recentCert?.type ?? cert?.type,
      }
    });
  }

  const onItemClick = (value, key) => {
    if (isMandatory(key)) {
      return;
    }
    setTallyCert(recentCert => {
      return {
        ...recentCert,
        [key]: value ? userCert?.[key] : null,
      }
    });
  }

  const addSubItem = (value, key, boolValue) => {
    setTallyCert(recentCert => {
      const recentData = [...recentCert?.[key]];
      const index = recentData.findIndex(item => JSON.stringify(item) === JSON.stringify(value));

      if (!boolValue) {
        recentData?.splice(index, 1);
      } else {
        recentData?.push(value);
      }
      return {
        ...recentCert,
        [key]: recentData.length === 0 ? null : recentData
      }
    });
  }

  function findLanguageValue(value) {
    return certificateLang?.find(item => item.value === value);
  }


  return <View style={styles.modalBackgroud}>
    <View style={styles.divider} >
      <Text style={styles.title}>Select Infomation to Include in Tally</Text>
    </View>
    <View style={styles.content}>
      <ScrollView
        style={{ flex: 1 }}
      >
        {
          // tallyCert is cert selected by user for tally
          // userCert is all user cert available but not for tally
          Object.keys(userCert).map((key, index) => {
            const langObj = findLanguageValue(key);
            const data = userCert?.[key];

            if (isMandatory(key)) {
              return <View key={`${key}${index}`} />
            }
            if (data) {
              return <View
                key={`${key}${index}`}
              >
                <View
                  style={styles.contractItem}
                >
                  {
                    (!Array.isArray(data) && <CheckBox
                      disabled={isMandatory(key)}
                      value={tallyCert?.[key] !== null && tallyCert?.[key] !== undefined}
                      onValueChange={(newValue) => {
                        onItemClick(newValue, key);
                      }}
                    />)
                  }
                  <HelpText
                    label={langObj?.title ?? ''}
                    helpText={langObj?.help}
                    style={styles.label}
                  />
                </View>
                {
                  (Array.isArray(data)) && data?.map((d, index) => {
                    return <View
                      key={`${d}${index}`}
                      style={{ flexDirection: 'row', paddingHorizontal: 8, alignItems: 'center', paddingVertical: 16 }}
                    >
                      <CheckBox
                        disabled={isMandatory(key)}
                        value={tallyCert?.[key]?.map(cert => JSON.stringify(cert))?.includes(JSON.stringify(d))}
                        onValueChange={(newValue) => {
                          addSubItem(d, key, newValue);
                        }}
                      />
                      <Text>
                        {d.comment ?? d.address}
                      </Text>
                    </View>
                  })
                }
              </View>
            }
            return <View key={`${key}${index}`} />
          })
        }
      </ScrollView>
      <View style={styles.row}>
        <Button
          title="Cancel"
          onPress={onDismiss}
          style={styles.cancel}
          textColor={colors.black100}
        />
        <Button
          style={styles.restore}
          title="Restore"
          onPress={onRestoreCert}
        />
        <Button
          style={styles.update}
          title="Proceed"
          onPress={onUpdate}
        />
      </View>

      <Text style={{ marginTop: 16, fontFamily: 'inter' }}>NOTE: More information defines the quality of tally.</Text>
    </View>
  </View >
}

const styles = StyleSheet.create({
  modalBackgroud: {
    flex: 1,
    alignItems: 'flex-start',
    backgroundColor: colors.white,
  },
  content: {
    flex: 1,
    paddingHorizontal: 24,
  },
  row: {
    flexDirection: 'row',
    marginTop: 24,
  },
  contractItem: {
    flexDirection: 'row',
    paddingVertical: 8,
    backgroundColor: colors.brightgray,
  },
  title: {
    fontSize: 16,
    fontWeight: 'bold',
    fontFamily: 'inter'
  },
  label: {
    fontSize: 14,
    fontFamily: 'inter',
    marginStart: 12,
  },
  divider: {
    minWidth: "100%",
    borderBottomWidth: 1,
    borderBottomColor: colors.quicksilver,
    paddingBottom: 16,
    paddingHorizontal: 24,
    marginBottom: 16,
  },
  cancel: {
    flex: 1,
    backgroundColor: 'transparent',
    borderRadius: 12
  },
  restore: {
    marginStart: 7,
    flex: 1,
    borderRadius: 12
  },
  update: {
    marginStart: 7,
    flex: 1,
    backgroundColor: 'green',
    borderColor: 'green',
    borderRadius: 12
  }
})
