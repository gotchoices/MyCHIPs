export const parse = (url) => {
  const queryString = url?.split('?')[1];

  if(!queryString) {
    return {};
  }

  const queryObj = {};

  queryString.split('&')?.forEach((query) => {
    const [key, value] = query?.split('=');

    if(key !== undefined && value != undefined) {
      queryObj[key] = value;
    }
  });

  return queryObj;
}
