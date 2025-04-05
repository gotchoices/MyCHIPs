/**
 * Utility functions for repairing tally certificates and signatures
 */
import { Alert } from 'react-native';
import { promptBiometrics } from '../services/biometrics';
import { reassertCertificate, reassertSignature } from '../services/tally';
import { showError } from './error';
import Toast from 'react-native-toast-message';

/**
 * Repair a tally's signature with the current user's signing key
 * 
 * @param {Object} wm - Wyseman connection
 * @param {number|string} tally_seq - Tally sequence number
 * @param {Function} onComplete - Optional callback after operation completes (successful or not)
 */
export const repairTallySignature = async (wm, tally_seq, onComplete) => {
  if (!tally_seq) {
    Alert.alert("Error", "Cannot re-sign: tally information is missing");
    onComplete?.();
    return;
  }
  
  Alert.alert(
    "Confirm Re-signing",
    "Are you sure you want to force a new signature on this tally? This will replace the existing signature with one created using your current key.",
    [
      { text: "Cancel", style: "cancel", onPress: () => onComplete?.() },
      {
        text: "Re-sign",
        onPress: async () => {
          try {
            // Use biometrics to confirm user identity before proceeding
            await promptBiometrics("Use biometrics to confirm re-signing");
            
            // Execute the backend operation without waiting for response
            reassertSignature(wm, tally_seq)
              .then(() => {
                // Nothing to do on success - backend will send notifications
              })
              .catch(err => {
                console.error('Error re-signing tally:', err);
                showError(err || {message: 'Failed to re-sign tally'});
              });
            
            // Move on immediately
            Toast.show({
              type: 'info',
              text1: 'Re-signing request sent',
              text2: 'The signature will be updated shortly',
            });
          } catch (err) {
            console.error('Biometric authentication failed:', err);
            showError(err || {message: 'Authentication failed'});
          } finally {
            onComplete?.();
          }
        }
      }
    ]
  );
};

/**
 * Repair a tally's certificate with the current user's public key
 * 
 * @param {Object} wm - Wyseman connection
 * @param {number|string} tally_seq - Tally sequence number
 * @param {Function} onComplete - Optional callback after operation completes (successful or not)
 */
export const repairTallyCertificate = async (wm, tally_seq, onComplete) => {
  if (!tally_seq) {
    Alert.alert("Error", "Cannot update certificate: tally information is missing");
    onComplete?.();
    return;
  }
  
  Alert.alert(
    "Confirm Certificate Update",
    "Are you sure you want to force a new certificate on this tally? This will replace the existing certificate with one containing your current public key.",
    [
      { text: "Cancel", style: "cancel", onPress: () => onComplete?.() },
      {
        text: "Update Certificate",
        onPress: async () => {
          try {
            // Use biometrics to confirm user identity before proceeding
            await promptBiometrics("Use biometrics to confirm certificate update");
            
            // Execute the backend operation without waiting for response
            reassertCertificate(wm, tally_seq)
              .then(() => {
                // Nothing to do on success - backend will send notifications
              })
              .catch(err => {
                console.error('Error updating certificate:', err);
                showError(err || {message: 'Failed to update certificate'});
              });
            
            // Move on immediately
            Toast.show({
              type: 'info',
              text1: 'Certificate update request sent',
              text2: 'The certificate will be updated shortly',
            });
          } catch (err) {
            console.error('Biometric authentication failed:', err);
            showError(err || {message: 'Authentication failed'});
          } finally {
            onComplete?.();
          }
        }
      }
    ]
  );
};