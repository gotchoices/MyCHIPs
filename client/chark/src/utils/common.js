export const round = (value, decimals) => {
  const temp = parseFloat(value + `e+${decimals}`);
  const result = Math.round(temp) + `e-${decimals}`;
  return parseFloat(result).toFixed(decimals);
}

export const random = (number = 10) => {
  return Math.floor(Math.random() * number);
}

export const getLinkHost = (url) => {
  return url?.split('?')?.[0]?.split('://')?.[1] ?? '';
}

export const isNil = (value) => {
  if(value === undefined || value === null)  {
    return true;
  }

  return false;
}
