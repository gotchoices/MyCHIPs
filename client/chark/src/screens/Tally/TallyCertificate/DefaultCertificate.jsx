import React, { useState, useEffect } from 'react';
import { View, StyleSheet, Text, Image, ScrollView, TouchableOpacity, Linking, Platform } from 'react-native';
import PropTypes from 'prop-types';
import { useSelector } from 'react-redux';
import FontAwesome from 'react-native-vector-icons/FontAwesome';
import FontAwesome5 from 'react-native-vector-icons/FontAwesome5';
import MaterialIcons from 'react-native-vector-icons/MaterialIcons';

import { colors } from '../../../config/constants';
import { WarningIcon, Warning_16 } from '../../../components/SvgAssets/SvgAssets';
import { checkKeyMatch } from '../../../utils/tally-verification';
import ValidityIcon from '../../../components/ValidityIcon';

// Enhanced DefaultCertificate component to display complete certificate info with boxes
const DefaultCertificate = (props) => {
  const { cert, tallyUuid, tallyEnt, tallySeq } = props;
  // Access the Redux store to get cached images by digest and validity statuses
  const { imagesByDigest } = useSelector((state) => state.avatar);
  const validityStatuses = useSelector(state => state.updateTally.validityStatuses || {});
  
  // State to check if certificate has a public key and if it matches current key
  const [hasPublicKey, setHasPublicKey] = useState(!!cert?.public);
  const [keyMatches, setKeyMatches] = useState(null);
  
  // Get the tally validity status from Redux if available
  // First try with tally_uuid, then fall back to composite key
  const tallyValidityStatus = tallyUuid ? 
    validityStatuses[tallyUuid] : 
    (tallyEnt && tallySeq ? validityStatuses[`${tallyEnt}-${tallySeq}`] : undefined);
  
  // Check for public key and key match when certificate changes
  useEffect(() => {
    setHasPublicKey(!!cert?.public);
    
    // Create a tally-like object for key checking
    const checkObject = {
      tally_type: 'stock', // Doesn't matter for our test
      json_core: {
        stock: {
          cert: cert
        }
      }
    };
    
    const checkKeyStatus = async () => {
      if (cert?.public) {
        const matches = await checkKeyMatch(checkObject);
        setKeyMatches(matches);
      } else {
        setKeyMatches(false);
      }
    };
    
    checkKeyStatus();
  }, [cert]);
  
  // Function to handle opening links
  const openLink = (url, type) => {
    if (!url) return;
    
    let fullUrl = url;
    
    try {
      switch (type) {
        case 'email':
          // Use Intent on Android for better email client handling
          if (Platform.OS === 'android') {
            const emailUrl = `mailto:${url}`;
            const intentUrl = `intent:${url}#Intent;action=android.intent.action.SENDTO;scheme=mailto;end`;
            
            // Try using Intent first
            Linking.canOpenURL(intentUrl)
              .then(supported => {
                if (supported) {
                  return Linking.openURL(intentUrl);
                } else {
                  // Fall back to standard mailto if intent isn't supported
                  console.log('Intent not supported, trying mailto');
                  return Linking.openURL(emailUrl);
                }
              })
              .catch(err => {
                console.error('Error with intent, trying mailto directly:', err);
                // Last resort: try mailto directly
                Linking.openURL(emailUrl).catch(err2 => {
                  console.error('Failed to open email client:', err2);
                  
                  // Final fallback - try explicit intent format for Gmail
                  Linking.openURL(
                    `intent:#Intent;action=android.intent.action.SENDTO;scheme=mailto;package=com.google.android.gm;S.android.intent.extra.EMAIL=${url};end`
                  ).catch(finalErr => {
                    console.error('All email client attempts failed:', finalErr);
                  });
                });
              });
          } else {
            // iOS handles mailto links well
            fullUrl = `mailto:${url}`;
            Linking.openURL(fullUrl).catch(err => {
              console.error(`Error opening email client:`, err);
            });
          }
          return; // Return early since we handled the link opening directly
          
        case 'phone':
          // Clean the phone number to only include digits, +, and possibly some formatting
          fullUrl = `tel:${url.replace(/[^0-9+\-\(\) ]/g, '')}`;
          break;
          
        case 'cell':
          // For cell phones, launch SMS instead of a call
          fullUrl = `sms:${url.replace(/[^0-9+\-\(\) ]/g, '')}`;
          break;
          
        case 'web':
          if (!url.startsWith('http://') && !url.startsWith('https://')) {
            fullUrl = `https://${url}`;
          }
          break;
          
        case 'address':
          // Create a maps URL based on the platform
          const query = encodeURIComponent(url);
          if (Platform.OS === 'ios') {
            fullUrl = `maps://?q=${query}`;
          } else {
            fullUrl = `https://maps.google.com/?q=${query}`;
          }
          break;
      }
      
      console.log(`Opening URL: ${fullUrl} (original: ${url}, type: ${type})`);
      
      // For non-email links (since we already handled email above)
      Linking.canOpenURL(fullUrl)
        .then(supported => {
          if (supported) {
            return Linking.openURL(fullUrl);
          } else {
            console.log(`Cannot open URL: ${fullUrl}`);
            // If the URL is not supported, try a fallback for some types
            if (type === 'web' && fullUrl.startsWith('https://')) {
              // Try http:// if https:// failed
              return Linking.openURL(fullUrl.replace('https://', 'http://'));
            }
          }
        })
        .catch(err => {
          console.error(`Error opening URL (${fullUrl}):`, err);
        });
    } catch (error) {
      console.error('Error processing URL:', error);
    }
  };
  
  // Function to find avatar file
  const getAvatarFile = () => {
    if (!cert?.file) return null;
    return cert.file.find(f => f.media === 'photo');
  };
  
  // Function to get place properties
  const getPlaceProperties = (place) => {
    if (!place) return [];
    
    // Get all properties of the place object
    return Object.entries(place).map(([key, value]) => {
      // Skip rendering these fields individually since we display them in their own fields
      if (['type', 'address', 'city', 'state', 'post', 'country'].includes(key)) {
        return null;
      }
      
      return (
        <View key={key} style={styles.fieldRow}>
          <FieldLabel>{`${key}`}</FieldLabel>
          <FieldValue>{typeof value === 'object' ? JSON.stringify(value) : String(value)}</FieldValue>
        </View>
      );
    }).filter(item => item !== null); // Remove null items
  };
  
  // Get icon for contact type
  const getContactIcon = (media) => {
    switch (media) {
      case 'email':
        return <FontAwesome name="envelope" size={16} color={colors.blue} />;
      case 'phone':
        return <FontAwesome name="phone" size={16} color={colors.blue} />;
      case 'cell':
        return <FontAwesome name="mobile" size={18} color={colors.blue} />;
      case 'web':
        return <FontAwesome name="globe" size={16} color={colors.blue} />;
      default:
        return <FontAwesome name="comment" size={16} color={colors.blue} />;
    }
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
        <View style={styles.nameRow}>
          {getNameFields()}
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
            <TouchableOpacity 
              key={`contact-${index}`} 
              style={styles.touchableRow}
              onPress={() => openLink(contact.address, contact.media)}
            >
              <View style={styles.contactRow}>
                <View style={styles.contactIcon}>
                  {getContactIcon(contact.media)}
                </View>
                <View style={styles.contactInfo}>
                  <FieldLabel>{`${contact.media}`}</FieldLabel>
                  <FieldValue>{contact.address}</FieldValue>
                </View>
                <View style={styles.launchIcon}>
                  <FontAwesome name="external-link" size={16} color={colors.blue} />
                </View>
              </View>
            </TouchableOpacity>
          ))}
        </SectionBox>
      )}
      
      {/* Address Information Box */}
      {cert?.place && cert.place.length > 0 && (
        <SectionBox title="place">
          {cert.place.map((place, index) => (
            <View key={`place-${index}`} style={styles.placeContainer}>
              <View style={styles.placeHeader}>
                <Text style={styles.placeType}>{place.type}</Text>
              </View>
              
              {place.address && (
                <TouchableOpacity 
                  style={styles.addressRow}
                  onPress={() => openLink(`${place.address}, ${place.city}, ${place.state} ${place.post}, ${place.country}`, 'address')}
                >
                  <View style={styles.addressContent}>
                    <Text style={styles.fieldValue}>{place.address}</Text>
                    <Text style={styles.fieldValue}>
                      {place.city ? place.city + ', ' : ''}
                      {place.state || ''} {place.post || ''}
                    </Text>
                    {place.country && (
                      <Text style={styles.fieldValue}>{place.country}</Text>
                    )}
                  </View>
                  <View style={styles.addressIcon}>
                    <FontAwesome name="map-marker" size={18} color={colors.blue} />
                  </View>
                </TouchableOpacity>
              )}
              
              {/* Display any additional place properties that may exist */}
              {getPlaceProperties(place)}
            </View>
          ))}
        </SectionBox>
      )}
      
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
      
      {/* Public Key Box - Always show this section */}
      <SectionBox 
        title="public"
        rightContent={
          <View style={styles.keyStatusIndicator}>
            {/* Use tallyValidityStatus if available, otherwise fall back to key-based validation */}
            {tallyValidityStatus ? (
              <ValidityIcon 
                status={tallyValidityStatus} 
                size={20}
                showTooltip={true}
                msgView="tallies_v_me"
                msgTag={!hasPublicKey ? "nocert" : (keyMatches === false ? "diffkey" : "valid")}
              />
            ) : (
              <>
                {!hasPublicKey && (
                  <ValidityIcon 
                    status="invalid" 
                    size={20}
                    showTooltip={true}
                    msgView="tallies_v_me"
                    msgTag="nocert"
                  />
                )}
                
                {hasPublicKey && keyMatches === false && (
                  <ValidityIcon 
                    status="warning" 
                    size={20}
                    showTooltip={true}
                    msgView="tallies_v_me"
                    msgTag="diffkey"
                  />
                )}
                
                {hasPublicKey && keyMatches === true && (
                  <ValidityIcon 
                    status="valid" 
                    size={20}
                    showTooltip={true}
                    msgView="tallies_v_me"
                    msgTag="valid"
                  />
                )}
              </>
            )}
          </View>
        }
      >
        {cert?.public ? (
          <ScrollView
            horizontal={false}
            style={styles.codeBlock}
          >
            <Text style={styles.jsonText}>
              {JSON.stringify(cert.public, null, 2)}
            </Text>
          </ScrollView>
        ) : (
          <View style={styles.emptyKeyContainer}>
            <FontAwesome name="key" size={24} color={colors.gray300} />
          </View>
        )}
      </SectionBox>
      
      {/* File Information Box */}
      {cert?.file && cert.file.length > 0 && (
        <SectionBox title="file">
          {cert.file.map((file, index) => (
            <View key={`file-${index}`} style={styles.fileContainer}>
              <Text style={styles.fileType}>{file.media}</Text>
              
              {file.format && (
                <Text style={styles.fileProperty}>format: {file.format}</Text>
              )}
              
              {file.comment && (
                <Text style={styles.fileProperty}>comment: {file.comment}</Text>
              )}
              
              {/* Display rectangular image for photo media */}
              {file.media === 'photo' && file.digest && (
                <View style={styles.imageContainer}>
                  {imagesByDigest[file.digest] ? (
                    <Image 
                      source={{ uri: imagesByDigest[file.digest] }}
                      style={styles.certificateImage}
                      resizeMode="cover"
                    />
                  ) : (
                    <View style={styles.placeholderContainer}>
                      <FontAwesome name="image" size={40} color={colors.gray300} />
                      <Text style={styles.placeholderText}>Image not in cache</Text>
                      <Text style={styles.digestText} numberOfLines={1} ellipsizeMode="middle">
                        {file.digest}
                      </Text>
                    </View>
                  )}
                </View>
              )}
              
              {file.digest && (
                <Text style={styles.digestText} numberOfLines={1} ellipsizeMode="middle">
                  digest: {file.digest}
                </Text>
              )}
            </View>
          ))}
        </SectionBox>
      )}
    </View>
  );
};

// Helper component for boxed sections
const SectionBox = ({ children, title, rightContent }) => (
  <View style={styles.sectionBox}>
    {title && (
      <View style={styles.sectionTitleRow}>
        <Text style={styles.sectionTitle}>{title}</Text>
        {rightContent}
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
  boxHeader: {
    flexDirection: 'row',
    justifyContent: 'space-between',
    alignItems: 'flex-start',
  },
  keyStatusContainer: {
    alignItems: 'flex-end',
  },
  iconWrapper: {
    flexDirection: 'row',
    alignItems: 'center',
    marginBottom: 4,
    backgroundColor: colors.gray7,
    paddingHorizontal: 8,
    paddingVertical: 4,
    borderRadius: 12,
  },
  iconText: {
    fontFamily: 'inter',
    fontSize: 12,
    color: colors.gray900,
    marginLeft: 4,
  },
  sectionBox: {
    backgroundColor: colors.gray5,
    borderWidth: 1,
    borderColor: colors.gray7,
    borderRadius: 8,
    padding: 16,
    marginBottom: 12,
  },
  sectionTitleRow: {
    flexDirection: 'row',
    justifyContent: 'space-between',
    alignItems: 'center',
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
  nameRow: {
    flexDirection: 'row',
    flexWrap: 'wrap',
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
  imageContainer: {
    alignItems: 'center',
    justifyContent: 'center',
    marginVertical: 10,
  },
  certificateImage: {
    width: 200,
    height: 150,
    borderRadius: 8,
    borderWidth: 1,
    borderColor: colors.gray7,
  },
  fieldRow: {
    marginBottom: 8,
  },
  touchableRow: {
    marginBottom: 10,
  },
  contactRow: {
    flexDirection: 'row',
    alignItems: 'center',
    paddingVertical: 5,
  },
  contactIcon: {
    width: 24,
    justifyContent: 'center',
    alignItems: 'center',
    marginRight: 8,
  },
  contactInfo: {
    flex: 1,
  },
  launchIcon: {
    width: 24,
    justifyContent: 'center',
    alignItems: 'center',
  },
  addressRow: {
    flexDirection: 'row',
    marginBottom: 8,
  },
  addressContent: {
    flex: 1,
  },
  addressIcon: {
    width: 30,
    justifyContent: 'center',
    alignItems: 'center',
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
    marginBottom: 3,
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
  placeContainer: {
    backgroundColor: colors.gray7,
    borderRadius: 6,
    padding: 10,
    marginBottom: 10,
  },
  placeHeader: {
    marginBottom: 5,
  },
  placeType: {
    fontFamily: 'inter',
    fontSize: 14,
    fontWeight: '600',
    color: colors.blue3,
  },
  fileContainer: {
    backgroundColor: colors.gray7,
    borderRadius: 6,
    padding: 10,
    marginBottom: 10,
  },
  fileType: {
    fontFamily: 'inter',
    fontSize: 14,
    fontWeight: '600',
    color: colors.blue3,
    marginBottom: 5,
  },
  fileProperty: {
    fontFamily: 'inter',
    fontSize: 13,
    color: colors.black,
    marginBottom: 3,
  },
  digestText: {
    fontFamily: 'inter',
    fontSize: 12,
    color: colors.gray300,
    marginTop: 5,
  },
  placeholderContainer: {
    width: 120,
    height: 120,
    backgroundColor: colors.gray7,
    borderRadius: 8,
    justifyContent: 'center',
    alignItems: 'center',
    padding: 10,
  },
  placeholderText: {
    fontFamily: 'inter',
    fontSize: 12,
    color: colors.gray300,
    marginTop: 10,
    textAlign: 'center',
  },
  publicKeyHeader: {
    flexDirection: 'row',
    justifyContent: 'flex-end',
    marginBottom: 10,
  },
  keyStatusIndicator: {
    flexDirection: 'row',
    justifyContent: 'flex-end',
  },
  emptyKeyContainer: {
    backgroundColor: colors.gray7,
    padding: 16,
    borderRadius: 8,
    alignItems: 'center',
    justifyContent: 'center',
    height: 100,
  },
  emptyKeyText: {
    fontFamily: 'inter',
    fontSize: 14,
    color: colors.gray500,
    fontStyle: 'italic',
  }
});

DefaultCertificate.propTypes = {
  name: PropTypes.string.isRequired,
  cuid: PropTypes.string.isRequired,
  email: PropTypes.string,
  agent: PropTypes.string.isRequired,
  cert: PropTypes.object,
  tallyUuid: PropTypes.string,
  tallyEnt: PropTypes.string,
  tallySeq: PropTypes.number,
};

export default DefaultCertificate;
