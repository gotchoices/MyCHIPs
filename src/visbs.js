//Support class for visual balance sheet graphs
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
// TODO:
//- Convert parts applicable to both urnet and user balance sheet
//- Urnet still works
//- Build single-user balance sheet for app

const CHIPmult = 1000
const gapAngle = 0.005			//Gap between slices
const startAngle = Math.PI / 2		//Start/end on East axis
const endAngle = Math.PI / 2*5
const minTextAngle = Math.PI / 8	//Display sum if pie slice bigger than this
const truncAgent = 6			//Show this many digits of agent ID

const neutral = '#DDD'			//Halfway between asset and liability
const maxNwColor  = "hsl(230,50%,40%)"	//Positive, assets
const minNwColor  = "hsl(350,50%,40%)"	//Negative, liabilities
const maxChipP = "hsl(200,100%,30%)"	//Darkest positive CHIP
const minChipP = "hsl(200,100%,70%)"	//Lightest positive CHIP
const maxChipN = "hsl(10,100%,30%)"	//Darkest negative CHIP
const minChipN = "hsl(10,100%,70%)"	//Lightest negative CHIP
var D3 = null;
var fontSize = 18;
var gen = {}
var ringData = [
    {tag: 'nw', rad: 30, title: 'Net Worth'},
    {tag: 'al', rad: 20, title: 'Assets & Liabilities'},
    {tag: 'ch', rad: 30, title: 'CHIP Tallies'}
]

var InitVisBS = function(d3) {		//Configure the module
  D3 = d3

  gen.pieGen = D3.pie()			//Pie-chart angle generator
    .startAngle(startAngle).endAngle(endAngle).padAngle(gapAngle)
    .sort(null)				//Already sorted
    .value(d => Math.abs(d.net))
  gen.posNwColor = D3.interpolate(neutral, maxNwColor)	//Pie slice color tables
  gen.negNwColor = D3.interpolate(neutral, minNwColor)
  gen.posChColor = D3.interpolate(maxChipP, minChipP)	//Backwards to accommodate reverse index
  gen.negChColor = D3.interpolate(maxChipN, minChipN)

}

class UserVisBS {				//Build an object for a user and its peers
  constructor(uRec, rData = ringData) {
    let lastRad = 0
      , slice = 0

    for (let i = 0; i < rData.length; i++) {	//Initialize pie/ring data
      let ring = rData[i]
//console.log("ring:", i, ring)
      ring.iRad = lastRad
      lastRad = ring.oRad = lastRad + ring.rad
      ring.pathGen = D3.arc()		//Generates pie-chart sections
        .cornerRadius(3).innerRadius(ring.iRad).outerRadius(ring.oRad)
    }
    this.userRadius = lastRad
    this.ringData = rData
    this.shades = {			//Separate gradient for positive/negative
      true:  D3.quantize(gen.posChColor, Math.max(2, uRec.assets)),	//positive
      false: D3.quantize(gen.negChColor, Math.max(2, uRec.liabs))	//negative
    }
    uRec.lookup = {}
    uRec.tallies.sort((a,b) => (a.net - b.net)).forEach(tally => {
      let idx = tally.net >= 0 ? uRec.tallies.length - (++slice) : slice++
      tally.color = this.shades[tally.net >= 0][idx]
      uRec.lookup[tally.uuid] = tally			//tally lookup table by uuid
    })
  }
  
  user(tag, uRec) {			//Generate control object for a user node
//console.log("User", tag, uRec.peer_cid, uRec.tallies)
    let { lookup, latest } = uRec
    let paths = []
      , textCmds = []
      , radius = this.userRadius

    for (let i = 0; i < this.ringData.length; i++) {	//Generate pie ring/sections
      let ring = this.ringData[i]
        , { tag, pathGen, oRad } = ring
        , arcs
      if (tag == 'nw') {
        let color = uRec.net >= 0 ? gen.posNwColor(uRec.net / uRec.asset) : gen.negNwColor(uRec.net / uRec.liab)
          , items = [{net:uRec.net, color}]
        arcs = gen.pieGen(items)			//Generate net-worth circle
      } else if (tag == 'al') {
        let items = [{net:uRec.liab, color:'red'}, {net:uRec.asset, color:'blue'}]
        arcs = gen.pieGen(items)			//Generate assets/liabilities ring
      } else if (tag == 'ch') {
        arcs = gen.pieGen(uRec.tallies)			//Generate outer CHIP ring
      }
      arcs.forEach(arc => {
        let d = arc.data
          , pathData = pathGen(arc)
        d.cent = tag == 'nw' ? [0,0] :  pathGen.centroid(arc)	//Save centroid for placement algorithm
//console.log("A", i, tag, arc, d)
        d.hub = {					//Connection point
          a: (arc.startAngle + arc.endAngle - Math.PI) / 2,
          r: this.userRadius
        }
        d.arc = arc					//Access to arc from tally object
        if (arc.endAngle - arc.startAngle > minTextAngle) {
          let [x, y] = d.cent
          textCmds.push(`<text x="${x}" y="${y}" dominant-baseline="middle" text-anchor="middle">${d.net}</text>`)
        }
        paths.push(`<path d="${pathData}" fill="${d.color}"/>`)
      })
    }
      let body = `
      <g stroke="black" stroke-width="0.5">
        ${paths.join('\n')}
        <circle r="${radius}" fill="url(#radGrad)"/>
        <text x="${-radius}" y="${-radius -fontSize/2}" style="font:normal ${fontSize}px sans-serif";>
          ${uRec.peer_cid}:${uRec.peer_agent.slice(-truncAgent)}
        </text>
        ${textCmds.join('\n')}
      </g>`
//console.log("User body:", body, width, height)
    return {state: {body, radius}, lookup, inside: true, latest}
  }
  
  peer(part, user, tally) {			//Generate SVG code for a peer node
    let [ cid, agent ] = part.split(':')
      , xOff = fontSize / 2
      , yOff = fontSize + 3
      , max = Math.max(cid.length + 2, agent.length + 6)	//take tspan into account
      , width = max * fontSize * 0.5,	w2 = width / 2
      , height = fontSize * 4,		h2 = height / 2
      , radius = w2
      , text = `
      <text x="${xOff}" y="${yOff}" style="font:normal ${fontSize}px sans-serif;">
        <tspan x="${-w2 + xOff}" y="${-h2 + yOff}">${cid}</tspan>
        <tspan x="${-w2 + xOff}" y="${-h2 + yOff * 2}">${agent.slice(-truncAgent)}</tspan>
        <tspan x="${-w2 + xOff}" y="${-h2 + yOff * 3}">${tally.net}</tspan>
      </text>`
      , rect = `x="${-w2}" y="${-h2}" rx="${yOff}" ry="${yOff}" width="${width}" height="${height}"`
      , body = `
      <g stroke="black" stroke-width="1">
        <rect ${rect} fill="${tally.color}"/>
        <rect ${rect} fill="url(#radGrad)"/>
        ${text}
      </g>`
      , ends = [{x:0, y:-h2}, {x:w2, y:0}, {x:0, y:h2}, {x:-w2, y:0}]
//console.log("Peer ends", ends)
    return {state: {body, radius}, ends, user, tally, inside: false}
  }

}

module.exports = {InitVisBS, UserVisBS}
