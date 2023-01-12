import React, { useState } from 'react';
import PropTypes from 'prop-types';
import {
  View,
  Text,
  TouchableWithoutFeedback,
  TouchableOpacity,
  StyleSheet,
} from 'react-native';
import Toast from 'react-native-toast-message';

import Button from '../../../components/Button';

import { colors } from '../../../config/constants';

const ChangePrimary = (props) => {
  const items = props.items; 
  const rowField = props.rowField;
  const primaryField = props.primaryField;
  const seqField = props.seqField;

  const [loading, setLoading] = useState(false);

  const onSave = () => {
    setLoading(true);
    props.savePrimary().then(() => {
      Toast.show({
        type: 'success',
        text1: 'Changes saved successfully.',
        position: 'bottom',
      });
    }).finally(() => {
      setLoading(false);
      props.onCancel();
    })
  }

  return (
    <View style={styles.container}>
      <View style={styles.header}>
        <Text style={styles.title}>{props.title}</Text>
      </View>

      {
        !items?.length && (
          <Text style={{ padding: 10 }}>No items found</Text>
        )
      }

      <View style={styles.body}>
        {
          items.map((item, index) => (
            <Item
              key={index}
              value={item[rowField]}
              primary={item[primaryField]}
              seq={item[seqField]}
              onPrimaryChange={props.onPrimaryChange}
              selectedPrimary={props.selectedPrimary}
            />
          ))
        }

        <View style={styles.action}>
          <View style={[styles.actionItem, { marginRight: '4%' }]}>
            <TouchableWithoutFeedback
              onPress={props.onCancel}
            >
              <View style={{ borderColor: colors.blue, borderWidth: 1, paddingVertical: 7 }}>
                <Text style={{ color: colors.blue, alignSelf: 'center' }}>Cancel</Text>
              </View>
            </TouchableWithoutFeedback>
          </View>
          {
            !!items.length && (
              <View style={styles.actionItem}>
                <Button 
                  onPress={onSave}
                  disabled={loading}
                  title="Save Changes"
                />
              </View>
            )
          }
        </View>
      </View>
    </View>
  )
}

function Item(props) {
  const isSelected = props.selectedPrimary === props.seq;

  return (
    <View style={[styles.item, isSelected ? styles.selectedItem : {}]}>
      <Text>{props.value}</Text>

      {
        props.primary ? (
          <Text style={styles.primary}>Primary</Text>
        ) : (
          <TouchableOpacity onPress={() => props.onPrimaryChange(props.seq)}>
            <Text style={styles.setPrimary}>Set as Primary</Text>
          </TouchableOpacity>
        )
      }
    </View>
  )
}


const styles = StyleSheet.create({
  container: {
    width: '100%',
    backgroundColor: colors.white,
  },
  header: {
    padding: 10,
    borderBottomWidth: 1,
    borderBottomColor: colors.brightgray,
  },
  title: {
    color: colors.black,
    fontWeight: 'bold',
    fontSize: 14,
  },
  body: {
    padding: 10,
  },
  item: {
    padding: 10,
    marginBottom: 10,
    flexDirection: 'row',
    backgroundColor: colors.antiflashwhite,
    justifyContent: 'space-between',
  },
  primary: {
    color: colors.quicksilver,
    fontWeight: '700',
  },
  setPrimary: {
    color: colors.blue,
    fontWeight: '700',
  },
  action: {
    paddingVertical: 16,
    flexDirection: 'row',
  },
  actionItem: {
    width: '48%',
  },
  selectedItem: {
    borderColor: colors.blue,
    borderWidth: 1
  }
});

ChangePrimary.propTypes = {
  items: PropTypes.array.isRequired,
  title: PropTypes.string.isRequired,
  rowField: PropTypes.string.isRequired,
  seqField: PropTypes.string.isRequired,
  primaryField: PropTypes.string.isRequired,
  onCancel: PropTypes.func.isRequired,
  onPrimaryChange: PropTypes.func.isRequired,
  savePrimary: PropTypes.func.isRequired,
  selectedPrimary: PropTypes.number,
}

export default ChangePrimary;
