import ReactNativeFS from 'react-native-fs';

// Function to save the JSON string to a file
const saveJSONToFile = async (jsonString) => {
  try {
    const directoryPath = ReactNativeFS.DocumentDirectoryPath;
    const filePath = `${directoryPath}/data.json`;

    // Write the JSON string to the file
    await ReactNativeFS.writeFile(filePath, jsonString, 'utf8');
    console.log('File saved successfully!');
    return filePath;
  } catch (error) {
    console.log('Error saving the file:', error);
    return null;
  }
};

// Function to initiate the file download
const downloadFile = async (jsonString) => {
  var path = ReactNativeFS.DownloadDirectoryPath + '/key.json';
  console.log("File Path ==> ", path);

  // write the file
  ReactNativeFS.writeFile(path, jsonString, 'utf8')
    .then((success) => {
      console.log('File Written==>', success);
    })
    .catch((err) => {
      console.log("Error==>", err.message);
    });
};

export default downloadFile;



/* 


  return;
  const filePath = await saveJSONToFile(jsonString);
  console.log("File Path==>", filePath);
  if (filePath) {

    // ReactNativeFS.downloadFile({
    //   fromUrl: `file://${filePath}`,
    //   toFile: filePath,
    // }).promise.then((response) => {
    //   console.log('File downloaded successfully!', response);
    //   // Additional handling after the file is downloaded
    // }).catch((error) => {
    //   console.log('Error downloading the file:', error);
    //   // Additional error handling
    // });

    // Share the file with the user
    // Share.open({
    //   url: `file://${filePath}`,
    //   type: 'application/json',
    //   failOnCancel: false,
    // })
    //   .then(() => {
    //     console.log('File shared successfully!');
    //     // Additional handling after the file is shared
    //   })
    //   .catch((error) => {
    //     console.log('Error sharing the file:', error);
    //     // Additional error handling
    //   });
  }


*/