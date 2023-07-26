//TODO: Not a complete set of tests but tries a couple things
import assessTallyRisk from "../src/riskAssess.js"

let testCertificates = {
	good: {
		date: "2022-01-11T09:39:06.443-07:00",
		name: {
			first: "Thomas",
			surname: "Well",
			prefer: "Tom"
		},
		type: "p",
		chad: {
			cid: "tom_well",
			agent: "Zzyzx",
			host: "mychips.org",
			port: 65430
		},
		place: [
			{
				post: "00630-1930",
				type: "mail",
				city: "Jackson",
				state: "MS",
				address: "630 Cornell Way",
				country: "US"
			 }
		],
		public: "KEY_HERE",
		connect: [
			{
				media: "phone",
				address: "888-123-7777"
			},
			{
				media: "email",
				address: "soul@mychips.org"
			}
		],
		identity: {
			birth: {
				date: "1930-06-30",
				name: "Thomas Sow Well",
				place: {
					city: "Gastonia",
					post: "13245-1951",
					state: "NC",
					address: "91 Hoover",
					country: "US"
				}
			},
			state: {
				id: "987-0-465-06073-3",
				country: "US"
			}
		}
	},
	oddHost: {
		date: "2022-01-11T09:39:06.443-07:00",
		name: {
			first: "Thomas",
			surname: "Well",
			prefer: "Tom"
		},
		type: "p",
		chad: {
			cid: "tom_well",
			agent: "Zzyzx",
			host: "kaboom.chip",
			port: 65430
		},
		place: [
			{
				post: "00630-1930",
				type: "mail",
				city: "Jackson",
				state: "MS",
				address: "630 Cornell Way",
				country: "US"
			 }
		],
		public: "KEY_HERE",
		connect: [
			{
				media: "phone",
				address: "888-123-7777"
			},
			{
				media: "email",
				address: "soul@mychips.org"
			}
		],
		identity: {
			birth: {
				date: "1930-06-30",
				name: "Thomas Sow Well",
				place: {
					city: "Gastonia",
					post: "13245-1951",
					state: "NC",
					address: "91 Hoover",
					country: "US"
				}
			},
			state: {
				id: "987-0-465-06073-3",
				country: "US"
			}
		}
	},
}

let testCreditTerms = {
  good: {
    limit: 0,
    call: 30,
  },
  medium: {
    limit: 25,
    call: 20,
  },
  highLimit: {
    limit: 200,
    call: 30,
  },
  bad: {
    limit: 200,
    call: 1000,
  },
}

let testTallies = {
  good: {
    version: "1",
    uuid: "9e61301c-86aa-5835-9ea1-25adf13eaf3c",
    date: new Date(Date.now()).toString(),
    note: "A good tally",
    stock: {
      cert: testCertificates.good,
      terms: testCreditTerms.good,
    },
    foil: {
      cert: testCertificates.good,
      terms: testCreditTerms.good,
    },
    agree: {
      domain: "mychips.org",
      name: "standard",
      version: "0.99",
    },
    sign: {
      foil: "GOOD SIGNATURE",
      stock: "GOOD SIGNATURE",
      digest: "GOOD HASH",
    },
  },
  medium: {
    version: "1",
    uuid: "9e61301c-86aa-5835-9ea1-25adf13eaf3c",
    date: new Date(Date.now()).toString(),
    note: "A good tally",
    stock: {
      cert: testCertificates.oddHost,
      terms: testCreditTerms.good,
    },
    foil: {
      cert: testCertificates.good,
      terms: testCreditTerms.good,
    },
    agree: {
      domain: "mychips.org",
      name: "standard",
      version: "0.99",
    },
    sign: {
      foil: "GOOD SIGNATURE",
      stock: "GOOD SIGNATURE",
      digest: "GOOD HASH",
    },
  },
  highLimit: {
    version: "1",
    uuid: "9e61301c-86aa-5835-9ea1-25adf13eaf3c",
    date: new Date(Date.now()).toString(),
    note: "A good tally",
    stock: {
      cert: testCertificates.good,
      terms: testCreditTerms.highLimit,
    },
    foil: {
      cert: testCertificates.good,
      terms: testCreditTerms.good,
    },
    agree: {
      domain: "mychips.org",
      name: "standard",
      version: "0.99",
    },
    sign: {
      foil: "GOOD SIGNATURE",
      stock: "GOOD SIGNATURE",
      digest: "GOOD HASH",
    },
  }
}

test("A good tally has low risk", () => {
  let risk = assessTallyRisk(testTallies.good)
  console.log("GOOD RISK IS:", risk)
  expect(risk.level).toBe("Low")
})

test("A oddHost tally has medium risk", () => {
  let risk = assessTallyRisk(testTallies.medium)
  console.log("ODD RISK IS:", risk)
  expect(risk.level).toBe("Medium")
})

test("A high limit tally has high risk", () => {
  let risk = assessTallyRisk(testTallies.highLimit)
  console.log("HIGH LIMIT RISK IS:", risk)
  expect(risk.level).toBe("High")
})
