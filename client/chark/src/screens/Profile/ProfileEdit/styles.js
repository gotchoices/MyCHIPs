import { StyleSheet } from 'react-native';

import { colors } from '../../../config/constants';

const styles = StyleSheet.create({
  container: {
    backgroundColor: colors.white,
    margin: 10,
  },
  header: {
    paddingHorizontal: 10,
    flexDirection: 'row',
    paddingVertical: 8,
    marginTop: 14,
    justifyContent: 'space-between',
    borderBottomWidth: 1,
    borderBottomColor: colors.lightgray,
  },
  headerText: {
    color: colors.black,
    fontSize: 14,
  },
  body: {
    paddingVertical: 12,
    paddingHorizontal: 10,
  },
  addButton: {
    flexDirection: 'row',
    justifyContent: 'center',
    alignItems: 'center',
    padding: 8,
    borderRadius: 5,
    backgroundColor: colors.white,
    borderWidth: 1,
    borderColor: colors.blue ,
    marginBottom: 32,
  }
});

export default styles;
