import React from "react";

import Share from '../../components/Share';
import useMessageText from "../../hooks/useMessageText";
import useTitle from "../../hooks/useTitle";
import { useLiftsPayMeText } from '../../hooks/useLanguage';
import useSocket from '../../hooks/useSocket';

const RequestShare = (props) => {
  const { wm } = useSocket();
  const { json = {}, link } = props.route.params;
  const { messageText } = useMessageText();
  const charkText = messageText?.chark?.msg;
  const liftsPayText = useLiftsPayMeText(wm)

  const text = {
    share: charkText?.share,
    link: charkText?.link,
    qr: charkText?.qr,
  }

  const linkHtml = link;
  const url = json?.url;
  const message = `${json.title ?? ''} \n\n${json?.message ?? ''} \n\n${url}`;

  useTitle(props.navigation, charkText?.share?.title)

  return (
    <Share
      qrData={url}
      linkHtml={linkHtml}
      shareTitle={liftsPayText?.msg?.request?.title ?? ''}
      message={message}
      text={text}
    />
  );
};

export default RequestShare;
