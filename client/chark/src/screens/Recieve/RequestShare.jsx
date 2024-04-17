import React from "react";

import Share from '../../components/Share';
import useMessageText from "../../hooks/useMessageText";
import useTitle from "../../hooks/useTitle";

const RequestShare = (props) => {
  const { json = {}, link } = props.route.params;
  const { messageText } = useMessageText();
  const charkText = messageText?.chark?.msg;

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
      shareTitle={'Request Chit'}
      message={message}
      text={text}
    />
  );
};

export default RequestShare;
