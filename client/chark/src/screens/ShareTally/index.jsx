import React, { useState, useEffect } from 'react';
import {
  StyleSheet,
} from 'react-native';
import Share from '../../components/Share';

import { colors } from '../../config/constants';
import useSocket from '../../hooks/useSocket';
import { request } from '../../services/request';
import { random } from '../../utils/common';

const ShareTally = (props) => {
  const tally_id = props.route?.params?.tally_id;
  const { wm } = useSocket();

  const [invite, setInvite] = useState();

  const tallyObj = invite?.json;
  const linkHtml = invite?.link;
  const tallyUrl = tallyObj?.url;

  const message = `${tallyObj?.title ?? ''} \n\n${tallyObj?.message ?? ''} \n\n${tallyUrl}`;

  useEffect(() => {
    const spec = {
      name: 'invite',
      view: 'mychips.tallies_v_me',
      data: {
        keys: [{ tally_seq: tally_id }],
        options: {
          reuse: true,
          format: ['json', 'link']
        }
      }
    }

    request(wm, `_invite_ref_json_${random(1000)}`, 'action', spec).then((data) => {
      const json = data?.[0];
      const link = data?.[1];
      console.log(link, 'link')

      setInvite({
        json,
        link
      })
    }).catch((e) => {
      console.log("Sharing Exception", e);
    });
  }, [tally_id])

  if(!invite) {
    return false;
  }

  return (
    <Share
      qrData={tallyUrl}
      linkHtml={linkHtml}
      shareTitle="Share Tally"
      message={message}
    />
  )
}

const actionItem = {
  borderWidth: 1,
  borderColor: colors.blue,
  marginHorizontal: '1%',
  justifyContent: 'center',
  alignItems: 'center',
  paddingVertical: 8,
  borderRadius: 5,
  marginBottom: 8,
}

const styles = StyleSheet.create({
  container: {
    flex: 1,
    width: '100%',
    backgroundColor: colors.white,
  },
  tab: {
    flexDirection: 'row',
    margin: 20,
  },
  tabItem: {
    padding: 8,
    width: '50%',
    borderWidth: 1,
    alignItems: 'center',
    justifyContent: 'center',
    borderColor: colors.blue,
  },
  tabText: {
    color: colors.black,
    fontWeight: '700',
  },
  activeTab: {
    backgroundColor: colors.blue,
  },
  activeText: {
    color: colors.white,
  },
  action: {
    paddingHorizontal: 10,
  },
  cancel: {
    ...actionItem,
  },
  share: {
    ...actionItem,
    backgroundColor: colors.blue,
  },
  qrView: {
    alignItems: 'center',
    paddingVertical: 32,
    backgroundColor: colors.white,
    marginVertical: 10,
  },
});

// ShareTally.propTypes = {
//   onCancel: PropTypes.func.isRequired,
//   json: PropTypes.object,
//   link: PropTypes.string,
// }

export default ShareTally;
