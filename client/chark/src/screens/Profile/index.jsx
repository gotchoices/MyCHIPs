import React, { useState } from 'react';
import {
  View,
  StyleSheet,
  ScrollView,
  TextInput,
  Text,
  Button,
} from 'react-native';

const Profile = () => {
  const [profile, setProfile] = useState({
    email: '',
    phone: '',
    mailingAddress: '',
    physicalAddress: '',
    socialSecurityNumber: '',
    birthDate: '',
    birthAddress: '',
  });

  const onChange = (name) => {
    return (value) => {
      setProfile({
        ...profile,
        [name]: value,
      });
    }
  }

  const onSave = () => {
    console.log(profile);
  }

  return (
    <ScrollView style={{ marginBottom: 55 }}>
      <View style={styles.container}>
        <View style={styles.formControl}>
          <Text style={styles.label}>Email</Text>
          <TextInput 
            style={styles.input}
            onChangeText={onChange('email')}
          />
        </View>

        <View style={styles.formControl}>
          <Text style={styles.label}>Phone</Text>
          <TextInput 
            style={styles.input}
            onChangeText={onChange('phone')}
          />
        </View>

        <View style={styles.formControl}>
          <Text style={styles.label}>Mailing Address</Text>
          <TextInput 
            style={styles.input}
            onChangeText={onChange('mailingAddress')}
          />
        </View>

        <View style={styles.formControl}>
          <Text style={styles.label}>Physical Address</Text>
          <TextInput 
            style={styles.input}
            onChangeText={onChange('physicalAddress')}
          />
        </View>

        <View style={styles.formControl}>
          <Text style={styles.label}>Social Security Number</Text>
          <TextInput 
            style={styles.input}
            onChangeText={onChange('socialSecurityNumber')}
          />
        </View>

        <View style={styles.formControl}>
          <Text style={styles.label}>Birth date</Text>
          <TextInput 
            style={styles.input}
            onChangeText={onChange('birthDate')}
          />
        </View>

        <View style={styles.formControl}>
          <Text style={styles.label}>Birth Address</Text>
          <TextInput 
            style={styles.input}
            onChangeText={onChange('birthAddress')}
          />
        </View>

        <Button title="Save" onPress={onSave} />
      </View>
    </ScrollView>
  )
}

const styles = StyleSheet.create({
  container: {
    flex: 1,
    margin: 10,
    padding: 10,
    backgroundColor: '#fff',
  },
  formControl: {
    marginVertical: 10,
  },
  label: {
    fontWeight: 'bold',
    marginBottom: 8,
  },
  input: {
    backgroundColor: '#F2F4F7',
  },
});

export default Profile;
