export const round = (value, decimals) => {
  const temp = parseFloat(value + `e+${decimals}`);
  const result = Math.round(temp) + `e-${decimals}`;
  return parseFloat(result);
}

export const random = (number = 10) => {
  return Math.floor(Math.random() * number);
}

export const getLinkHost = (url) => {
  return url?.split('?')?.[0]?.split('://')?.[1] ?? '';
}
