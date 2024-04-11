import Toast from 'react-native-toast-message';

export const showError = (err) => {
  const title = err?.lang?.title;
  const description = err?.lang?.help;

  let obj;
  if(!title) {
    obj = {
      text1: description ?? err.message,
    }
  } else {
    obj = {
      text1: title,
      text2: description ?? err.message,
    }
  }

  return Toast.show({
    type: 'error',
    ...obj,
  })
}
