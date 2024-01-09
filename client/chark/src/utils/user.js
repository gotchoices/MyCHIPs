let pktId = 1;

export function query_user(wm) {
  return new Promise((resolve, reject) => {
    wm.request(
      pktId++,
      "select",
      {
        view: "base.ent_v",
        table: "base.curr_eid",
        params: [],
      },
      (data) => {
        resolve(data);
      }
    );
  });
}

export const getTallyName = (item) => {
  if (item.part_cert?.type === "o") {
    return `${item.part_cert?.name}`;
  }

  const { first, middle, surname } = item.part_cert?.name || {};
  return `${first || ""}${middle ? " " + middle + " " : ""}${
    surname || ""
  }`;
};

export const sortTalliesAlphabetically = (tallies) => {
  const sortedArray = [...tallies].sort((a, b) => {
    const tallyName1 = getTallyName(a);
    const tallyName2 = getTallyName(b);

    return tallyName1.localeCompare(tallyName2);
  });

  return sortedArray;
};

export const sortTallies = (tallies, field, descending = false) => {
  const sorteTallies = tallies.slice().sort((a, b) => {
    const valueA =
      field === "tally_date"
        ? new Date(a[field])
        : parseFloat(a[field]);

    const valueB =
      field === "tally_date"
        ? new Date(b[field])
        : parseFloat(b[field]);

    return descending ? valueB - valueA : valueA - valueB;
  });

  return sorteTallies;
};
