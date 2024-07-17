import React from 'react';
import { useSelector } from 'react-redux';
import moment from 'moment';
import PropTypes from 'prop-types';
import CheckBox from '@react-native-community/checkbox'
import { 
  View,
  Text,
  StyleSheet,
} from 'react-native';

import Avatar from '../../components/Avatar';

import { colors } from '../../config/constants';

const CustomCertificateItem = (props) => {
  const type = props.type;
  const data = props.data;
  const { imagesByDigest } = useSelector((state) => state.avatar);
  const file = imagesByDigest?.[props?.data?.digest];

  const onCheckBoxChange = (value) => {
    if(props.onCheckBoxChange) {
      props.onCheckBoxChange(value)
    }
  }

  return (
    <View style={styles.container}>
      <View style={styles.content}>
        {type === 'place' && (
          <Place
            type={data?.type}
            comment={data?.comment}
            address={data?.address}
            city={data?.city}
            state={data?.state}
            code={data?.code}
            country={data?.country}
          />
        )}

        {type === 'birth' && (
          <Birth
            birth={data}
          />
        )}

        {type === 'connect' && (
          <Connect
            type={data?.type}
            media={data?.media}
            address={data?.address}
          />
        )}

        {type === 'state' && (
          <State
            country={data?.country}
            id={data?.id}
          />
        )}

        {type === 'chad' && (
          <Chad
            cuid={data.cuid}
            agent={data.agent}
          />
        )}

        {type === 'date' && data?.date && (
          <Text style={styles.value}>
            {moment(data.date).format('YYYY-MM-DD')}
          </Text>
        )}

        {type === 'file' && (
          <File
            {...(props?.data ?? {})}
            file={file}
          />
        )}
      </View>
      
      <View style={styles.checkbox}>
        <CheckBox
          value={props.selected}
          onValueChange={onCheckBoxChange}
          disabled={props.disabled ?? false}
          tintColors={{
            true: props.disabled ? colors.gray : colors.blue,
          }}

        />
      </View>
    </View>
  )
}

function Place(props) {
  return (
    <View>
      {(!!props.type || !!props.comment) && (
        <Text style={styles.value}>
          {props.type}: {props.comment}
        </Text>
      )}

      {!!props.address && (
        <Text style={styles.value}>
          {props.address}
        </Text>
      )}

      {!!props.city && (
        <Text style={styles.value}>
          {props.city}, {props.state} {props.code}
        </Text>
      )}

      {!!props.country && (
        <Text style={styles.value}>
          {props.country}
        </Text>
      )}
    </View>
  )
}

function Birth(props) {
  const birth = props?.birth;

  const city = birth?.place?.city ?? ''
  const state = birth?.place?.state ?? ''
  const code = birth?.place?.code ?? ''
  const cityText = `${city ? city : ''}${state? ' ,' + state: ''}${code ? ' ' + code : ''}`

  return (
    <View>
      {!!birth?.name?.length && (
        <Text style={styles.value}>
          {birth?.name[0]?.name}
        </Text>
      )}

      {!!birth.date && (
        <Text style={styles.value}>
          {birth.date}
        </Text>
      )}

      {!!birth?.place?.address && (
        <Text style={styles.value}>
          {birth?.place?.address}
        </Text>
      )}

      {!!cityText && (
        <Text style={styles.value}>
          {cityText}
        </Text>
      )}

      {!!birth?.place?.country && (
        <Text style={styles.value}>
          {birth?.place?.country}
        </Text>
      )}
    </View>
  )
}

function Connect(props) {
  return (
    <View>
      <Text style={styles.value}>
        {props.media}: {props.address}
      </Text>
    </View>
  )
}

function State(props) {
  return (
    <View>
      <Text style={styles.value}>
        {`${props.country ? props.country : ''} ${props.id ? ':' + props.id : '' }`}
      </Text>
    </View>
  )
}

function Chad(props) {
  return (
    <View>
      <Text style={styles.value}>
        Agent: {props.agent}
      </Text>

      <Text style={styles.value}>
        CUID: {props.cuid}
      </Text>
    </View>
  )
}

function File(props) {
  return (
    <View>
      <Text style={[styles.value, { marginBottom: 5 }]}>
        {props.comment}
      </Text>

      
        {props.file ? (
          <Avatar style={{ borderRadius: 0 }} avatar={props.file} />
        ): (
          <Text style={styles.value}>
            {props.digest}
          </Text>
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
    flexDirection: 'row',
    justifyContent: 'space-between',
    alignItems: 'center',
    marginVertical: 8,
  },
  label: {
    ...font,
    fontSize: 12,
    color: colors.gray300,
  },
  value: {
    ...font,
    fontSize: 14,
    color: colors.black,
  },
  content: {
    width: '90%',
    padding: 10,
    borderWidth: 0.5,
    borderRadius: 5,
    borderColor: colors.gray6,
  },
  checkbox: {
    width: '10%'
  },
});

CustomCertificateItem.propTypes = {
  type: PropTypes.string.isRequired,
  data: PropTypes.any,
  selected: PropTypes.bool.isRequired,
  onCheckBoxChange: PropTypes.func,
  disabled: PropTypes.bool,
};

export default CustomCertificateItem;
