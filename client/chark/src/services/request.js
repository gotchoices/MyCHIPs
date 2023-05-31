export const request = (wm, uniqueId, action, spec) => {
  return new Promise((resolve, reject) => {
    wm.request(uniqueId, action, spec, (data, err) => {
      if (err) {
        return reject(err)
      }
      resolve(data);
    })
  })
}

export const langRegister = (wm, uniqueId, view) => {
  return new Promise((resolve) => {
    wm.register(uniqueId, view, (data, err) => {
      if (err) {
        resolve({})
      }

      resolve(data?.col ?? {});
    })
  })
}

