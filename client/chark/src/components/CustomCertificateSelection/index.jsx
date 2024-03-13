import React from 'react';
import PropTypes from 'prop-types';
import { 
  View,
  StyleSheet,
} from 'react-native';

import HelpText from '../HelpText';
import CustomCertificateItem from './CustomCertificateItem';

import { colors } from '../../config/constants';

const CustomCertificateSelection = (props) => {
  const chad = props.chad;
  const date = props.date;
  const place = props.place;
  const birth = props.birth;
  const state = props.state;
  const connect = props.connect
  const file = props.file;

  return (
    <View style={styles.content}>
      {!!place?.ids?.length && (
        <View style={styles.certDetail}>
          <HelpText
            style={styles.label}
            label={'place_text'}
          />
          
          {place.ids.map((id, index) => (
            <CustomCertificateItem 
              key={index}
              type="place"
              data={place.byId[id]}
              selected={place.byId[id]?.selected}
              onCheckBoxChange={props.onPlaceChange(id)}
            />
          ))}
        </View>
      )}

      {!!birth?.data && (
        <View style={styles.certDetail}>
          <HelpText
            style={styles.label}
            label={'birth_text'}
          />
          
          <CustomCertificateItem 
            type="birth"
            data={birth?.data}
            selected={birth?.selected}
            onCheckBoxChange={props.onBirthChange}
          />
        </View>
      )}

      {!!file?.ids?.length && (
        <View style={styles.certDetail}>
          <HelpText
            style={styles.label}
            label={'file_text'}
          />
          
          {file.ids.map((id, index) => (
            <CustomCertificateItem 
              key={index}
              type="file"
              data={file.byId[id]}
              selected={file.byId[id]?.selected}
              onCheckBoxChange={props.onFileChange(id)}
            />
          ))}
        </View>
      )}

      {!!connect?.ids?.length && (
        <View style={styles.certDetail}>
          <HelpText
            style={styles.label}
            label={'connect_text'}
          />
          
          {connect.ids?.map?.((id, index) => (
            <CustomCertificateItem 
              key={index}
              type="connect"
              data={connect.byId[id]}
              selected={connect.byId[id]?.selected}
              onCheckBoxChange={props.onConnectChange(id)}
            />
          ))}
        </View>
      )}

      {!!state?.data && (
        <View style={styles.certDetail}>
          <HelpText
            style={styles.label}
            label={'state_text'}
          />
          
          <CustomCertificateItem 
            type="state"
            data={state.data}
            selected={state?.selected}
            onCheckBoxChange={props.onStateChange}
          />
        </View>
      )}

      {!!chad && (
        <View style={styles.certDetail}>
          <HelpText
            style={styles.label}
            label={'chad_text'}
          />
          
          <CustomCertificateItem 
            type="chad"
            data={chad}
            disabled={true}
            selected={true}
          />
        </View>
      )}

      {!!date && (
        <View style={styles.certDetail}>
          <HelpText
            style={styles.label}
            label={'date_text'}
          />
          
          <CustomCertificateItem 
            type="date"
            data={{ date }}
            disabled={true}
            selected={true}
          />
        </View>
      )}
    </View>
  )
}

const font = {
  fontFamily: 'inter',
  fontWeight: '500',
}

const styles = StyleSheet.create({
  container: {
    flex: 1,
  },
  content: {
    flex: 1,
    marginTop: 30,
  },
  header: {
    flexDirection: 'row',
    justifyContent: 'center',
  },
  headerIcon: {
    position: 'absolute',
    left: 0,
    top: -3,
  },
  headerText: {
    fontFamily: 'inter',
    fontSize: 18,
    fontWeight: '500',
    color: colors.black,
  },
  selectContainer: {
    flexDirection: 'row',
    justifyContent: 'flex-end' 
  },
  select: {
    ...font,
    color: colors.blue,
    flexDirection: 'row',
    justifyContent: 'flex-end',
    textDecorationLine: 'underline',
  },
  certificates: {
    marginTop: 10,
  },
  label: {
    ...font,
    fontSize: 14,
    color: colors.gray300,
  },
  certDetail: {
    marginBottom: 16,
  },
});

CustomCertificateSelection.propTypes = {
  chad: PropTypes.object,
  date: PropTypes.any,
  place: PropTypes.any,
  birth: PropTypes.any,
  state: PropTypes.any,
  connect: PropTypes.any,
  onPlaceChange: PropTypes.func.isRequired,
  onBirthChange: PropTypes.func.isRequired,
  onConnectChange: PropTypes.func.isRequired,
  onStateChange: PropTypes.func.isRequired,
}

export default CustomCertificateSelection;
