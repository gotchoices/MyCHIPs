import React from 'react';
import { View, StyleSheet, Text, Image, ScrollView } from 'react-native';
import PropTypes from 'prop-types';
import FontAwesome from 'react-native-vector-icons/FontAwesome';

import { colors } from '../../../config/constants';
import Avatar from '../../../components/Avatar';

// Enhanced DefaultCertificate component to display complete certificate info with boxes
const DefaultCertificate = (props) => {
  const { cert } = props;
  
  // Function to find avatar file
  const getAvatarFile = () => {
    if (!cert?.file) return null;
    return cert.file.find(f => f.media === 'photo');
  };
  
  // Generate name field display
  const getNameFields = () => {
    if (!cert?.name) return [];
    
    return Object.entries(cert.name).map(([key, value]) => (
      <View key={key} style={styles.nameField}>
        <Text style={styles.nameLabel}>{`name.${key}`}</Text>
        <Text style={styles.nameValue}>{value}</Text>
      </View>
    ));
  };
  
  return (
    <View>
      {/* Basic Information Box */}
      <SectionBox>
        <View style={styles.basicHeader}>
          <View style={styles.nameRow}>
            {getNameFields()}
          </View>
          
          {getAvatarFile() && (
            <View style={styles.avatarContainer}>
              <Avatar 
                source={{ uri: `data:image/jpeg;base64,${getAvatarFile().digest}` }} 
                size={60}
              />
            </View>
          )}
        </View>
        
        <View style={styles.divider} />
        
        <View style={styles.fieldRow}>
          <FieldLabel>type</FieldLabel>
          <FieldValue>{cert?.type || ''}</FieldValue>
        </View>
        
        <View style={styles.fieldRow}>
          <FieldLabel>date</FieldLabel>
          <FieldValue>{cert?.date || ''}</FieldValue>
        </View>
      </SectionBox>
      
      {/* CHAD Box */}
      <SectionBox title="chad">
        <View style={styles.fieldRow}>
          <FieldLabel>chad.cuid</FieldLabel>
          <FieldValue>{props.cuid}</FieldValue>
        </View>
        
        <View style={styles.fieldRow}>
          <FieldLabel>chad.agent</FieldLabel>
          <FieldValue>{props.agent}</FieldValue>
        </View>
        
        {cert?.chad?.host && (
          <View style={styles.fieldRow}>
            <FieldLabel>chad.host</FieldLabel>
            <FieldValue>{cert.chad.host}</FieldValue>
          </View>
        )}
        
        {cert?.chad?.port && (
          <View style={styles.fieldRow}>
            <FieldLabel>chad.port</FieldLabel>
            <FieldValue>{cert.chad.port.toString()}</FieldValue>
          </View>
        )}
      </SectionBox>
      
      {/* Contact Information Box */}
      {(cert?.connect || []).length > 0 && (
        <SectionBox title="connect">
          {(cert?.connect || []).map((contact, index) => (
            <View key={`contact-${index}`} style={styles.fieldRow}>
              <FieldLabel>{`${contact.media}`}</FieldLabel>
              <FieldValue>{contact.address}</FieldValue>
            </View>
          ))}
        </SectionBox>
      )}
      
      {/* Address Information Boxes */}
      {cert?.place && cert.place.length > 0 && cert.place.map((place, index) => (
        <SectionBox key={`place-${index}`} title={`place[${index}] - ${place.type}`}>
          <View style={styles.fieldRow}>
            <FieldLabel>address</FieldLabel>
            <FieldValue>{place.address}</FieldValue>
          </View>
          
          <View style={styles.fieldRow}>
            <FieldLabel>city</FieldLabel>
            <FieldValue>{place.city}</FieldValue>
          </View>
          
          <View style={styles.fieldRow}>
            <FieldLabel>state</FieldLabel>
            <FieldValue>{place.state}</FieldValue>
          </View>
          
          <View style={styles.fieldRow}>
            <FieldLabel>post</FieldLabel>
            <FieldValue>{place.post}</FieldValue>
          </View>
          
          <View style={styles.fieldRow}>
            <FieldLabel>country</FieldLabel>
            <FieldValue>{place.country}</FieldValue>
          </View>
        </SectionBox>
      ))}
      
      {/* Identity Information Box */}
      {cert?.identity && (
        <SectionBox title="identity">
          {cert.identity.birth && (
            <View style={styles.fieldRow}>
              <FieldLabel>birth.date</FieldLabel>
              <FieldValue>{cert.identity.birth.date || ''}</FieldValue>
            </View>
          )}
          
          {cert.identity.state && (
            <View style={styles.fieldRow}>
              <FieldLabel>state.country</FieldLabel>
              <FieldValue>{cert.identity.state.country || ''}</FieldValue>
            </View>
          )}
        </SectionBox>
      )}
      
      {/* Public Key Box */}
      {cert?.public && (
        <SectionBox title="public">
          <ScrollView
            horizontal={false}
            style={styles.codeBlock}
          >
            <Text style={styles.jsonText}>
              {JSON.stringify(cert.public, null, 2)}
            </Text>
          </ScrollView>
        </SectionBox>
      )}
      
      {/* File Information Boxes */}
      {cert?.file && cert.file.length > 0 && cert.file.map((file, index) => (
        <SectionBox key={`file-${index}`} title={`file[${index}] - ${file.media}`}>
          {file.format && (
            <View style={styles.fieldRow}>
              <FieldLabel>format</FieldLabel>
              <FieldValue>{file.format}</FieldValue>
            </View>
          )}
          
          {file.comment && (
            <View style={styles.fieldRow}>
              <FieldLabel>comment</FieldLabel>
              <FieldValue>{file.comment}</FieldValue>
            </View>
          )}
          
          {file.digest && (
            <View style={styles.fieldRow}>
              <FieldLabel>digest</FieldLabel>
              <FieldValue numberOfLines={1} ellipsizeMode="middle">{file.digest}</FieldValue>
            </View>
          )}
          
          {/* Display image preview for photo media */}
          {file.media === 'photo' && file.digest && (
            <View style={styles.imagePreviewContainer}>
              <Image 
                source={{ uri: `data:image/jpeg;base64,${file.digest}` }}
                style={styles.imagePreview}
                resizeMode="contain"
              />
            </View>
          )}
        </SectionBox>
      ))}
    </View>
  );
};

// Helper component for boxed sections
const SectionBox = ({ children, title }) => (
  <View style={styles.sectionBox}>
    {title && (
      <View style={styles.sectionTitleRow}>
        <Text style={styles.sectionTitle}>{title}</Text>
      </View>
    )}
    {children}
  </View>
);

// Helper components for field labels and values
const FieldLabel = ({ children }) => (
  <Text style={styles.fieldLabel}>{children}</Text>
);

const FieldValue = ({ children, ...props }) => (
  <Text style={styles.fieldValue} {...props}>{children}</Text>
);

const styles = StyleSheet.create({
  sectionBox: {
    backgroundColor: colors.gray5,
    borderWidth: 1,
    borderColor: colors.gray7,
    borderRadius: 8,
    padding: 16,
    marginBottom: 12,
  },
  sectionTitleRow: {
    borderBottomWidth: 1,
    borderBottomColor: colors.gray7,
    paddingBottom: 8,
    marginBottom: 12,
  },
  sectionTitle: {
    fontFamily: 'inter',
    fontSize: 14,
    fontWeight: '600',
    color: colors.blue3,
  },
  divider: {
    height: 1,
    backgroundColor: colors.gray7,
    marginVertical: 10,
  },
  basicHeader: {
    flexDirection: 'row',
    justifyContent: 'space-between',
    alignItems: 'flex-start',
  },
  nameRow: {
    flexDirection: 'row',
    flexWrap: 'wrap',
    flex: 1,
    marginRight: 8,
  },
  nameField: {
    marginRight: 12,
    marginBottom: 6,
  },
  nameLabel: {
    fontFamily: 'inter',
    fontSize: 12,
    color: colors.gray300,
    fontWeight: '500',
  },
  nameValue: {
    fontFamily: 'inter',
    fontSize: 16,
    fontWeight: '500',
    color: colors.black,
  },
  avatarContainer: {
    marginLeft: 'auto',
  },
  fieldRow: {
    marginBottom: 8,
  },
  fieldLabel: {
    fontFamily: 'inter',
    fontSize: 12,
    color: colors.gray300,
    fontWeight: '500',
  },
  fieldValue: {
    fontFamily: 'inter',
    fontSize: 14,
    color: colors.black,
    fontWeight: '400',
  },
  codeBlock: {
    backgroundColor: colors.gray7,
    padding: 10,
    borderRadius: 5,
    maxHeight: 200,
  },
  jsonText: {
    fontFamily: 'monospace',
    fontSize: 12,
    color: colors.darkGray,
  },
  imagePreviewContainer: {
    marginTop: 8,
    alignItems: 'center',
    justifyContent: 'center',
  },
  imagePreview: {
    width: 200,
    height: 200,
    borderRadius: 4,
  },
});

DefaultCertificate.propTypes = {
  name: PropTypes.string.isRequired,
  cuid: PropTypes.string.isRequired,
  email: PropTypes.string,
  agent: PropTypes.string.isRequired,
  cert: PropTypes.object,
};

export default DefaultCertificate;
