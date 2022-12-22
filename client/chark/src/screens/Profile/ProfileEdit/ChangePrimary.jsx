import React, { useState } from 'react';
import PropTypes from 'prop-types';
import {
  View,
  Text,
  Button,
  TouchableWithoutFeedback,
  StyleSheet,
} from 'react-native';

import { colors } from '../../../config/constants';

const Item = (props) => {
  return (
    <View style={styles.item}>
      <Text>{props.value}</Text>

      {
        props.primary ? (
          <Text style={styles.primary}>Primary</Text>
        ) : (
          <TouchableWithoutFeedback onPress={() => props.onPrimaryChange(props.seq)}>
            <Text style={styles.setPrimary}>Set as Primary</Text>
          </TouchableWithoutFeedback>
        )
      }
    </View>
  )
}

const ChangePrimary = (props) => {
  const items = props.items; 
  const rowField = props.rowField;
  const primaryField = props.primaryField;

  const [loading, setLoading] = useState(false);

  const onSave = () => {
    setLoading(true);
    props.savePrimary().finally(() => {
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
              seq={item[props.seqField]}
              onPrimaryChange={props.onPrimaryChange}
            />
          ))
        }

        <View style={styles.action}>
          <View style={[styles.actionItem, { marginRight: '4%' }]}>
            <Button 
              title="Cancel"
              onPress={props.onCancel}
            />
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
}

export default ChangePrimary;
