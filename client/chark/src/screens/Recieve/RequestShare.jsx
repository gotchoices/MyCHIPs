import React from "react";

import Share from '../../components/Share';

const RequestShare = (props) => {
  const { json = {}, link } = props.route.params;

  const linkHtml = link;
  const url = json?.url;
  const message = `${json.title ?? ''} \n\n${json?.message ?? ''} \n\n${url}`;

  return (
    <Share
      qrData={url}
      linkHtml={linkHtml}
      shareTitle="Request Chit"
      message={message}
    />
  );
};

export default RequestShare;
