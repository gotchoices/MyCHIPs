export const formatRandomString = (randomString) => {
  if (randomString) {
    const words = randomString.split('');

    const firstFourWords = words.slice(0, 4).join('');
    const lastFourWords = words.slice(-4).join('');

    const formattedString = `${firstFourWords}~${lastFourWords}`;

    return formattedString;
  }
  return "";
}
