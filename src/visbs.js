//Support class for visual balance sheet graphs (can run direct in browser and via webpack)
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
const VisBSConfig = {
  gapAngle:	0.005,			//Gap between slices
  startAngle:	Math.PI / 2,		//Start/end on East axis
  endAngle:	Math.PI / 2*5,
  minTextAngle:	Math.PI / 8,		//Display sum if pie slice bigger than this
  truncAgent:	6,			//Show this many digits of agent ID
  fontSize:	18,

  neutral:	"#DDD",			//Halfway between asset and liability
  maxNwColor:	"hsl(230,75%,40%)",	//Positive net worth
  minNwColor:	"hsl(350,75%,40%)",	//Negative
  assetColor:	"hsl(235,90%,50%)",	//Assets
  liabColor:	"hsl(355,90%,50%)",	//Liabilities
  maxChipP:	"hsl(200,100%,30%)",	//Darkest positive CHIP
  minChipP:	"hsl(200,100%,70%)",	//Lightest positive CHIP
  maxChipN:	"hsl(10,100%,30%)",	//Darkest negative CHIP
  minChipN:	"hsl(10,100%,70%)",	//Lightest negative CHIP

  ringData: [
    {tag: 'nw', rad: 30},
    {tag: 'al', rad: 20},
    {tag: 'ch', rad: 30},
  ]
}

var VisBSInit = function(config) {		//Configure the module
  Object.assign(VisBSConfig, config)		//User settings
}

class VisBSUser {				//Build an object for a user and its peers
  constructor(uRec, config) {
    let lastRad = 0
      , slice = 0

    Object.assign(this, VisBSConfig, config)

    this.gen = {}
    this.gen.pieGen = this.d3.pie()		//Pie-chart angle generator
      .startAngle(this.startAngle).endAngle(this.endAngle).padAngle(this.gapAngle)
      .sort(null)				//Already sorted
      .value(d => Math.abs(d.net))
    this.gen.posNwColor = this.d3.interpolate(this.neutral, this.maxNwColor)	//Pie slice color tables
    this.gen.negNwColor = this.d3.interpolate(this.neutral, this.minNwColor)
    
    this.gen.posChColor = this.d3.interpolate(this.maxChipP, this.minChipP)	//Backwards to accommodate reverse index
    this.gen.negChColor = this.d3.interpolate(this.maxChipN, this.minChipN)

    for (let i = 0; i < this.ringData.length; i++) {	//Initialize pie/ring data
      let ring = this.ringData[i]
//console.log("ring:", i, ring)
      ring.iRad = lastRad
      lastRad = ring.oRad = lastRad + ring.rad
      ring.pathGen = this.d3.arc()		//Generates pie-chart sections
        .cornerRadius(3).innerRadius(ring.iRad).outerRadius(ring.oRad)
    }
    this.userRadius = lastRad
    this.shades = {			//Separate gradient for positive/negative
      true:  this.d3.quantize(this.gen.posChColor, Math.max(2, uRec.assets)),	//positive
      false: this.d3.quantize(this.gen.negChColor, Math.max(2, uRec.liabs))	//negative
    }
    uRec.lookup = {}
    uRec.tallies.sort((a,b) => (a.net - b.net)).forEach(tally => {
      let idx = tally.net >= 0 ? uRec.tallies.length - (++slice) : slice++
      tally.color = this.shades[tally.net >= 0][idx]
      uRec.lookup[tally.uuid] = tally			//tally lookup table by uuid
    })
  }
  
  user(uRec) {				//Generate body data for a user node
//console.log("User", tag, uRec.peer_cid, uRec.tallies)
    let paths = []
      , textCmds = []
      , radius = this.userRadius

    for (let i = 0; i < this.ringData.length; i++) {	//Generate pie ring/sections
      let ring = this.ringData[i]
        , { tag, pathGen, oRad } = ring
        , arcs
      if (tag == 'nw') {
        let color = uRec.net >= 0 ? this.gen.posNwColor(uRec.net / uRec.asset) : this.gen.negNwColor(uRec.net / uRec.liab)
          , items = [{net:uRec.net, color}]
        arcs = this.gen.pieGen(items)			//Generate net-worth circle
      } else if (tag == 'al') {
        let items = [{net:uRec.liab, color: this.liabColor}, {net:uRec.asset, color: this.assetColor}]
        arcs = this.gen.pieGen(items)			//Generate assets/liabilities ring
      } else if (tag == 'ch') {
        arcs = this.gen.pieGen(uRec.tallies)			//Generate outer CHIP ring
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
        if (arc.endAngle - arc.startAngle > this.minTextAngle) {
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
        <text x="${-radius}" y="${-radius -this.fontSize/2}" style="font:normal ${this.fontSize}px sans-serif";>
          ${uRec.peer_cid}:${uRec.peer_agent.slice(-this.truncAgent)}
        </text>
        ${textCmds.join('\n')}
      </g>`
//console.log("User body:", body, width, height)
    return {body, radius}
  }
  
  peer(tally) {					//Generate SVG code for a peer node
    let { part } = tally
      , [ cid, agent ] = part.split(':')
      , xOff = this.fontSize / 2
      , yOff = this.fontSize + 3
      , max = Math.max(cid.length + 2, agent.length + 6)	//take tspan into account
      , width = max * this.fontSize * 0.5,	w2 = width / 2
      , height = this.fontSize * 4,		h2 = height / 2
      , radius = w2
      , text = `
      <text x="${xOff}" y="${yOff}" style="font:normal ${this.fontSize}px sans-serif;">
        <tspan x="${-w2 + xOff}" y="${-h2 + yOff}">${cid}</tspan>
        <tspan x="${-w2 + xOff}" y="${-h2 + yOff * 2}">${agent.slice(-this.truncAgent)}</tspan>
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
    return {body, radius, ends}
  }

}

if (typeof module !== 'undefined')		//For direct browser loads
  module.exports = {VisBSConfig, VisBSInit, VisBSUser}
