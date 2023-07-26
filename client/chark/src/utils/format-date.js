import moment from 'moment';
import { dateFormats } from '../config/constants';

export const formatDate = ({ date, format }) => {
  try {
    return moment(date).format(format ?? dateFormats.date);
  } catch (ex) {
    console.log("Date Format Ex ==> ", ex);
    return "";
  }
}



