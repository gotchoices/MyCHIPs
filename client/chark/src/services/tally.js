import { random } from '../utils/common';
import { langRegister } from './request';

export const getTallyText = (wm) => {
  const tallies = langRegister(wm, '_tally_lang' + random(), 'mychips.tallies');

  return Promise.all([
    tallies,
  ]).then(responses => {
    const result = responses.reduce((response, acc) => {
      return Object.assign(acc, response ?? {});
    }, {});

    return result;
  })
}

