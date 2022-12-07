import * as React from 'react';

import { RNCamera } from 'react-native-camera';
import { StyleSheet, Dimensions, View } from 'react-native';
//import { Client } from 'wyseman';

const { width, height } = Dimensions.get('window');
const credential = {"token":"ff2264abc8f0eb7f47e6fa0e6be82f50","expires":"2022-09-02T02:05:32.000Z","host":"mychips0","port":54320};

export default function CameraLogin() {
    const camera = React.useRef(null);

    React.useEffect(() => {
//        Client.connect(credential, ws => {});
        console.log("useEffect:", credential)
    }, [])

    return (
        <View style={styles.container}>
            <RNCamera
                ref={camera}
                style={styles.preview}
                type={RNCamera.Constants.Type.back}
                flashMode={RNCamera.Constants.FlashMode.on}
                androidCameraPermissionOptions={{
                    title: 'Permission to use camera',
                    message: 'We need your permission to use your camera',
                    buttonPositive: 'Ok',
                    buttonNegative: 'Cancel',
                }}
                androidRecordAudioPermissionOptions={{
                    title: 'Permission to use audio recording',
                    message: 'We need your permission to use your audio',
                    buttonPositive: 'Ok',
                    buttonNegative: 'Cancel',
                }}
                onBarCodeRead={(res) => {
                    console.log(res.data);
                }}
            />
        </View>
    )
}

const styles = StyleSheet.create({
    container: {
        width: width,
        height: height,
        resizeMode: 'cover'
    },
    preview: {
        width: width,
        height: height,
    },
});
