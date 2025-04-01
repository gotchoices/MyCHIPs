export default {
  keyTag: 'connectKey',
  chipsToDollar: 4.00,
};

export const dateFormats = {
  date: 'YYYY-MM-DD',
  dateTime: 'YYYY-MM-DD hh:mm a',
};

export const colors = {
  white: '#FFF',
  white100: '#F0F0F0',
  white200: '#E7E7E7',
  black: '#000',
  black100: '#344054',
  green: '#147013',
  blue: '#1570EF',
  blue2: '#2196F3',
  blue3: '#155CEF',
  red: '#D95656',
  gray100: '#F2F4F7',
  gray300: '#636363',
  gray500: '#667085',
  gray700: '#475467',
  gray5: '#F2F2F2',
  gray6: '#8A8A8A',
  gray7: '#DFDFDF',
  gray8: '#EDEDED',
  gray9: '#BDBDBD',
  gray10: '#9B9B9B',
  lightgray: '#d9d9d9',
  dimgray: '#686868',
  quicksilver: '#9f9f9f',
  brightgray: '#eeeeee',
  antiflashwhite: '#f3f3f3',
  snow: '#fbf9f9',
  mustardBrown: '#ce8805',
  orangeRed: '#ff4d4f',
  gray: '#BBBBBB',
  yellow: '#FFB422',

  connected: '#23C320',
  connecting: '#FFB422',
  disconnected: '#D95656',

};

export const keyServices = {
  publicKey: 'public_key',
  privateKey: 'private_key',
};

export const connectsObj = {
  email: {label: 'Email', link: 'mailto:'},
  phone: {label: 'Phone Number', link: 'tel:'},
  cell: {label: 'Cell Number', link: 'tel:'},
  web: {label: 'Website', link: 'https://'},
};

export const localStorage = {
  TallyPictures: 'TallyPictures',
};

export const KeyConfig = {
  name: 'ECDSA',
  namedCurve: 'P-521',
  hash: {name: 'SHA-384'}
};

// Number of units per CHIP (e.g., 1000 milliCHIPs = 1 CHIP)
export const CHIP_UNIT_FACTOR = 1000;

// Number of decimal places to display in CHIP amounts
export const CHIP_DECIMAL_PLACES = 3;

export const toastVisibilityTime = 10000;
