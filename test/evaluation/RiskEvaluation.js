/***
 * These weights decide how "bad" each type of infraction is
 * Used to compute the risk score (high being worse)
 * Score is in turn used to provide a "Low" "Medium" or "High" risk level
***/
//TODO review and decide weights
const defaultWeights = {
  nullTally: 50,
  unknownTallyVersion: 50,
  missingUUID: 50, 
  malformedUUID: 50, 
  missingNote: 1,
  malformedStockRecord: 50,
  malformedFoilRecord: 50,
  missingDate: 50,
  malformedDate: 10, //not too bad, might be human readable
  offByOneDate: 10,
  incorrectDate: 30,
  futureCertificateDate: 30,
  missingCertificate: 50,
  missingCertificateName: 50,
  missingCertificateEntityType: 10,
  incompleteCertificateName: 30,
  missingChipAddress: 50,
  missingCID: 50,
  missingAgentHost: 50,
  untrustedAgentHost: 10,
  unreachableChipAddress: 40,
  missingCertificatePublicKey: 50,
  missingCertificateConnect: 40,
  incompleteCertificateConnect: 20,
  missingCertificateIdentity: 50,
  missingCertificateBirthRecord: 30,
  incompleteCertificateBirthRecord: 30,
  missingStateId: 20,
  incompleteStateId: 20,
  missingCertificatePlace: 30,
  invalidCertificatePlace: 30,
  incompleteCertificatePlace: 20,
  missingCertificatePlaceInBirthRecord: 30,
  invalidCertificatePlaceInBirthRecord: 30,
  incompleteCertificatePlaceInBirthRecord: 20,
  missingUserCreditTerms: 50,
  missingPartnerCreditTerms: 50,
  userCreditExceedsLimit: 20,
  partnerCreditExceedsLimit: 30,
  shortUserCallPeriod: 30,
  longPartnerCallPeriod: 30,
  malformedAgreeRecord: 50,
  untrustedAgreeementTerms: 40,
  untrustedAgreeementVersion: 30,
  unknownInfraction: 1000, //big number helpful in debugging
}

/***
 * These options help us decide what is an infraction or not
 * They allow the user to customize the risk assesment 
***/
const defaultOptions = {
  acceptedAgreementDomains: ["mychips.org"],
  acceptedAgreementNames: ["standard"],
  acceptedAgreementVersions: ["0.99"],
  acceptedAgentHosts: ["mychips.org"], //the user might edit this to include only the host of the source of the tally proposal 
  userType: "foil", // "stock" | "foil"
  riskThresholds: {
    low: 0,
    medium: 10,
    high: 30,
  },
  creditTermThresholds: {
    userLimit: 4000, //don't give me more then ~10K USD of credit
    partnerLimit: 50, //give them only small credit. This option will be a common edit
    userCall: 30, //give me at least 30 days
    partnerCall: 30, //give them at most 30 days
  }
}

//TODO: Double check we never try to access a key in null or undefined
/***
 * This is the function the risk assessment service should call
 * Parameters:
   * tally : object that describes the tally initalization data
 * returns object:
 * {
 *   score: number
 *   level: string "Low" | "Medium" | "High"
 *   infractions: [string] with infraction identifiers
 * }
 * The infraction identifiers are the same as the keys of defaultWeights
 * The intent is that the client can use the identifier to lookup appropriate error text in the localized language
 ***/
export default function evaluateTallyRisk(tally, options=defaultOptions, weights=defaultWeights) {
  let infractions = []
  if (!tally) {
    infractions.push("nullTally")  
    //we can't do much from here return the bad news
    return generateResults(infractions, options, weights)
  }
  if (tally.version != "1") {
    infractions.push("unknownTallyVersion")  
    //we can't do much from here return the bad news
    return generateResults(infractions, options, weights)
  }

  if (!tally.uuid) infractions.push("missingUUID")
  else if (!tally.uuid?.match(/[\da-fA-F]{8}-[\da-fA-F]{4}-[\da-fA-F]{4}-[\da-fA-F]{4}-[\da-fA-F]{12}/)) {
    //not of the form:
    // xxxxxxxx-xxxx-xxxx-xxxx-xxxxxxxxxxxx
    // e.g. 9e61301c-86aa-5835-9ea1-25adf13eaf3c
    infractions.push("malformedUUID")
  }
  let dateInfractions = assessDateRisk(tally.date, options)
  infractions = [...infractions, ...dateInfractions]
  if (!tally.note) infractions.push("missingNote")
  if (!userRecordIsWellFormed(tally.stock)) {
    infractions.push("malformedStockRecord")
  }
  else {
    if (options.userType == "foil") {
      //only check the stock if it looks ok and we are the foil
      let userInfractions = assessCertificateRisk(tally.stock.cert, options)
      infractions = [...infractions, ...userInfractions]
    }
  }
  if (!userRecordIsWellFormed(tally.foil)) {
    infractions.push("malformedFoilRecord")
  }
  else {
    if (options.userType == "stock") {
      //only check the foil if it looks ok and we are the stock
      let userInfractions = assessCertificateRisk(tally.foil.cert, options)
      infractions = [...infractions, ...userInfractions]
    }
  }
  let termsInfractions = assessCreditTermsRisk(tally, options)
  infractions = [...infractions, ...termsInfractions]
  let agreeInfractions = assessAgreementRisk(tally.agree, options)
  infractions = [...infractions, ...agreeInfractions]
    
  return generateResults(infractions, options, weights)
}

function generateResults(infractions, options, weights) {
  //Add up all the weights connected with each infraction to get a score
  let score = infractions.reduce((a, v) => {
    let weight = weights[v] || weights.unknownInfraction
    return a + weight
  }, 0)
  let level = "Low" //default low
  if (score >= options.riskThresholds.medium) {
    //overwrite to medium if above threshold
    level = "Medium"
  }
  if (score >= options.riskThresholds.high) {
    //overwrite to high if above the threshold
    level = "High"
  }
  return {
    level,
    score,
    infractions,
  }
}

function userRecordIsWellFormed(stock) {
  if (!stock.hasOwnProperty("cert")) return false
  if (!stock.hasOwnProperty("terms")) return false
  return true
}

function assessDateRisk(date, options) {
  let infractions = []
  if (!date) infractions.push("missingDate")
  else {
    let recordDate = new Date(date)
    if (!recordDate) {
      infractions.push("malformedDate")
    }
    else {
      let currentDate = new Date(Date.now())
      let differenceMilliseconds = Math.abs(currentDate.getTime() - recordDate.getTime())
      let differenceDays = differenceMilliseconds / (1000 * 3600 * 24);
      if (differenceDays > 1 && differenceDays < 2) {
        infractions.push("offByOneDate")
      }
      else if (differenceDays >= 2) {
        infractions.push("incorrectDate")
      }
    }
  }
  return infractions
}

function assessCertificateRisk(cert, options) {
  //TODO Add risk based on our own list of blacklisted users 
  //If someone gets reported to us for breaking deals too often we will upgrade their risk
  //TODO Add risk based on known lift capability of a user
  if (!cert) {
    return ["missingCertificate"]
  }
  let infractions = []
  if (!cert.date) {
    infractions.push("missingDate")
  }
  let recordDate = new Date(cert.date)
  if (!recordDate) {
    infractions.push("malformedDate")
  }
  if (recordDate.getTime() > Date.now()) {
    infractions.push("futureCertificateDate")
  }
  if (!cert.name) {
    infractions.push("missingCertificateName")
  }
  if (!cert.type) {
    infractions.push("missingCertificateEntityType")
  }
  switch (cert.type) {
    case "c":
      //is a company
      if (!cert?.name.dba) {
        infractions.push("incompleteCertificateName")
      }
    case "p":
    default: //assume they are a person if not specified
      //is a person
      if (!cert?.name.surname) {
        infractions.push("incompleteCertificateName")
      }
      break
  }
  if (!cert.chad) {
    infractions.push("missingChipAddress")
  }
  if (!cert.chad?.cid) {
    infractions.push("missingCID")
  }
  if (!cert.chad?.host) {
    infractions.push("missingAgentHost")
  }
  if (!options.acceptedAgentHosts.includes(cert.chad?.host)) {
    infractions.push("untrustedAgentHost")
  }
  if (!testChadReachability(cert.chad).reachable) {
    infractions.push("unreachableChipAddress")
  }
  let placeInfractions = assessPlaceRisk(cert.place, options)
  infractions = [...infractions, ...placeInfractions]
  if (!cert.public) {
    infractions.push("missingCertificatePublicKey")
  }
  if (!cert.connect) {
    infractions.push("missingCertificateConnect")
  }
  if (!Array.isArray(cert.connect)) {
    cert.connect = [cert.connect]
  }
  let hasPhoneListed = cert.connect?.reduce((a, v) => {
    if (v?.media == "phone") {
      return !!v.address //make sure we have data for the address
    }
    return a
  }, false)
  if (!hasPhoneListed) {
    infractions.push("incompleteCertificateConnect")
  }
  let hasEmailListed = cert.connect?.reduce((a, v) => {
    if (v?.media == "email") {
      return !!v.address
    }
    return a
  }, false)
  if (!hasEmailListed) {
    infractions.push("incompleteCertificateConnect")
  }
  if (!cert.identity) {
    infractions.push("missingCertificateIdentity")
  }
  else {
    if (!cert.identity.birth) {
      infractions.push("missingCertificateBirthRecord")
    }
    else if (!cert.identity.birth.date) {
      infractions.push("incompleteCertificateBirthRecord")
    }
    else {
      let placeInfractions = assessPlaceRisk(cert.identity.birth.place).map(i => i + "InBirthRecord")
      infractions = [...infractions, ...placeInfractions]
    }
    if (!cert.identity.state) {
      infractions.push("missingStateId")
    }
    else if (!cert.identity.state.country || !cert.identity.state.id) {
      infractions.push("incompleteStateId")
    }
  }
  return infractions
}

function assessPlaceRisk(place, options) {
  //TODO Add risk based on blacklisted places in options?
  //  e.g Afganistan might be more risky than Canada
  //  TODO Add risk based on proximity to user? E.g. Location 800 miles away is risker then 20 miles away
  let infractions = []
  if (!place) {
    return ["missingCertificatePlace"]
  }
  if (!Array.isArray(place)) {
    place = [place]
  }
  let hasCompleteAddress = place.reduce((a, v) => {
    if (!verifyAddress(place).isValid) {
      //if we find one that looks weird push an infraction
      infractions.push("invalidCertificatePlace")
    }
    //if we allready found a complete record skip the rest
    if (a) return true 
    if (!v.address) {
      return false
    }
    if (!v.city) {
      return false
    }
    if (!v.country) {
      return false
    }
    if (v.country == "US" && !v.state) {
      return false
    }
    return true //We found a good address record
  }, false)
  if (!hasCompleteAddress) {
    infractions.push("incompleteCertificatePlace")
  }
  return infractions
}

function verifyAddress(place) {
  //TODO make sure postal code matches city
  //Check address against USPS database etc
  return {isValid: true}
}

function testChadReachability(chad) {
  //TODO send a network request to see if the host recognizes the user
  return {reachable: true}
}

function assessCreditTermsRisk(tally, options) {
  let stockTerms = tally?.stock?.terms
  let foilTerms = tally?.stock?.terms
  let userTerms = options.userType == "foil" ? foilTerms : stockTerms
  let partnerTerms = options.userType == "foil" ? stockTerms : foilTerms
  let infractions = []
  if (!userTerms) {
    infractions.push("missingUserCreditTerms")
  }
  if (!partnerTerms) {
    infractions.push("missingPartnerCreditTerms")
  }
  if (userTerms.limit > options.creditTermThresholds.userLimit) {
    infractions.push("userCreditExceedsLimit")
  }
  if (partnerTerms.limit > options.creditTermThresholds.partnerLimit) {
    infractions.push("partnerCreditExceedsLimit")
  }
  if (userTerms.call < options.creditTermThresholds.userCall) {
    infractions.push("shortUserCallPeriod")
  }
  if (partnerTerms.call > options.creditTermThresholds.partnerCall) {
    infractions.push("longPartnerCallPeriod")
  }
  return infractions
}

function assessAgreementRisk(agree, options) {
  let infractions = []
  if (!agree) return ["malformedAgreeRecord"]
  if (!options.acceptedAgreementDomains.includes(agree.domain)) {
    infractions.push("untrustedAgreementTerms") 
  }
  else if (!options.acceptedAgreementNames.includes(agree.name)) {
    infractions.push("untrustedAgreementTerms") 
  }
  else if (!options.acceptedAgreementVersions.includes(agree.version)) {
    infractions.push("untrustedAgreementVersion") 
  }
  return infractions
}

