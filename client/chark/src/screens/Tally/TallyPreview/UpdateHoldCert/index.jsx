import React, { useEffect, useState } from "react"
import { StyleSheet, Text, View } from "react-native"
import { colors } from "../../../../config/constants";
import Button from "../../../../components/Button";
import CheckBox from "@react-native-community/checkbox";
import useProfile from "../../../../hooks/useProfile";

const certLabel = {
  chad: "Custoner ID and Server",
  date: "Tally Updated Date",
  file: "Your Profile Picture",
  type: "User Type",
  name: "Your Name",
  place: "Your Addresses",
  public: "Your Public Key",
  connect: "Your contact details such as; Phone, Email, and Website",
  identity: "Your birth details containing; date, place, state, country and so on."
}

export const UpdateHoldCert = ({ onDismiss, onUpdateCert, tallyCurrentHoldCert }) => {
  const { personal } = useProfile();
  const [tallyCert, setTallyCert] = useState({ ...tallyCurrentHoldCert ?? {} });
  const [userCert, setUserCert] = useState({});

  useEffect(() => {
    const cert = personal?.cert;
    console.log("DEFAULT_CERT ==> ", JSON.stringify(cert));
    if (cert) {
      setTallyCert(recentCert => {
        return {
          ...recentCert,
          chad: recentCert?.chad ?? cert?.chad,
          date: recentCert?.date ?? cert?.date,
          file: recentCert?.file ?? cert?.file,
          name: recentCert?.nam ?? cert?.name,
        }
      });
      setUserCert(cert);
    }
  }, [personal])

  const onUpdate = () => {
    onUpdateCert(tallyCert);
  }

  const isMandatory = (key) => {
    if (key === 'chad' || key === 'date' || key === 'name' || key === 'file') {
      return true;
    } else {
      return false;
    }
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

  return <View style={styles.modalBackgroud}>
    <View style={styles.divider} >
      <Text style={styles.title}>Select Infomation to Include in Tally</Text>
    </View>
    <View style={styles.content}>
      {
        Object.keys(userCert).map((key, index) => {
          if (userCert?.[key]) {
            return <View
              key={`${key}${index}`}
              style={styles.contractItem}
            >
              <CheckBox
                disabled={isMandatory(key)}
                value={tallyCert?.[key] !== null && tallyCert?.[key] !== undefined}
                onValueChange={(newValue) => {
                  onItemClick(newValue, key);
                }}
              />
              <Text style={styles.label}>{certLabel[key]}</Text>
            </View>
          }
          return <View key={`${key}${index}`} />
        })
      }

      <View style={styles.row}>
        <Button
          title="Cancel"
          onPress={onDismiss}
          style={styles.cancel}
          textColor={colors.black100}
        />
        <Button
          style={styles.update}
          title="Continue"
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
    paddingHorizontal: 24,
    alignItems: 'flex-start',
  },
  row: {
    flexDirection: 'row',
    marginTop: 24,
  },
  contractItem: {
    flexDirection: 'row',
    justifyContent: 'center',
    alignItems: 'center',
    paddingVertical: 8,
    borderBottomColor: colors.gray100,
    borderBottomWidth: 1,
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
    flex: 1,
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
    marginEnd: 7,
    flex: 1,
    backgroundColor: 'transparent',
    borderRadius: 12
  },
  update: {
    marginStart: 7,
    flex: 1,
    borderRadius: 12
  }
})