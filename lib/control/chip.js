//Return estimate of CHIP value in terms of a standard currency
//Copyright MyCHIPs.org; See license in root of this package
// ----------------------------------------------------------------------------
//TODO:
//- 
const { log, buildContent, staticFile, errCode } = require('./common')
const Path = require('path')
const chipSql = `with
  chip as (select * from base.exchange where curr = 'XCH' order by sample desc limit 1),
  last as (select curr, base, max(sample) as sample from base.exchange group by 1,2)

  select
    chip.curr as chip, 
    chip.rate as chip_rate,
    fiat.curr as fiat,
    fiat.rate as fiat_rate, 
    chip.base as base, 
    trunc((chip.rate * fiat.rate)::numeric, 4) as rate,
    chip.sample as chip_sample, 
    fiat.sample as fiat_sample
      from  chip
      join  last on last.base = chip.base
      join  base.exchange fiat
        on fiat.curr = last.curr and fiat.base = last.base and fiat.sample = last.sample
    where fiat.curr = $1;`

// ----------------------------------------------------------------------------
function chip(info, cb, resource) {
  if (resource) return false			//No support for http calls
  let {data, view, message, db} = info
    , {options} = data
    , content, error
    , parms = [options?.curr ?? 'USD']		//;log.debug('chip:', options)

  db.query(chipSql, parms, (err, res) => {	//log.debug('  err:', err, ' res:', res, 'rows:', res?.rows ? res.rows[0] : null)
    let row = res?.rows?.length == 1 ? res.rows[0] : {}
    if (err) {
      log.error("Error in query for chip value:", err)
      error = errCode(view, 'GCH', err)		//Getting CHIP value
    }

    let makeContent = function(format) {
      switch (format) {
        case 'json':
          return row
        default:
          return `
            <div>${message('chip').title}:</div>
            1 CHIP ~ ${row.rate} ${row.fiat} as of ${row.fiat_sample}, ${row.chip}:${row.chip_sample}
          `
      }
    }
    if (!error)
      content = buildContent(options?.format, makeContent)
    cb(error, content)
  })
  return (false)
}

module.exports = {
  'mychips.users_v_me': {chip}
}
