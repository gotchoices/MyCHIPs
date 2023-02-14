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

export class VisBS {
  constructor(d3) {
    this.d3 = d3

    this.fontSize = 18;
    this.userRadius = 80;
    this.gen = {}
    this.ringData = [
      {tag: 'nw', rad: 30, title: 'Net Worth'},
      {tag: 'al', rad: 20, title: 'Assets & Liabilities'},
      {tag: 'ch', rad: 30, title: 'CHIP Tallies'}
    ]
    
    let lastRad = 0
    for (let i = 0; i < this.ringData.length; i++) {	//Initialize pie/ring data
      let ring = this.ringData[i]
//console.log("ring:", i, ring)
      ring.iRad = lastRad
      lastRad = ring.oRad = lastRad + ring.rad
      ring.pathGen = this.d3.arc()		//Generates pie-chart sections
        .cornerRadius(3).innerRadius(ring.iRad).outerRadius(ring.oRad)
    }
    this.userRadius = lastRad

    this.gen.pieGen = this.d3.pie()		//Pie-chart angle generator
      .startAngle(startAngle).endAngle(endAngle).padAngle(gapAngle)
      .sort(null)				//Already sorted
      .value(d => Math.abs(d.net))
    this.gen.posNwColor = this.d3.interpolate(neutral, maxNwColor)	//Pie slice color tables
    this.gen.negNwColor = this.d3.interpolate(neutral, minNwColor)
    this.gen.posChColor = this.d3.interpolate(maxChipP, minChipP)	//Backwards to accommodate reverse index
    this.gen.negChColor = this.d3.interpolate(maxChipN, minChipN)
    
  }
  
  shadeMap(assets, liabilities) {
    return {				//Separate gradient for positive/negative
      true:  this.d3.quantize(this.gen.posChColor, Math.max(2, assets)),	//positive
      false: this.d3.quantize(this.gen.negChColor, Math.max(2, liabilities))	//negative
    }
  }

  user(tag, userRec) {			//Generate control object for a user node
//console.log("User", tag, userRec.peer_cid, userRec.tallies)
    let { id, std_name, peer_cid, peer_agent, lookup, tallies, latest } = userRec
      , paths = []
      , radius
      , textCmds = []

    for (let i = 0; i < this.ringData.length; i++) {	//Generate pie ring/sections
      let ring = this.ringData[i]
        , { tag, pathGen, oRad } = ring
        , arcs
      if (tag == 'nw') {
        let color = userRec.net >= 0 ? this.gen.posNwColor(userRec.net / userRec.asset) : this.gen.negNwColor(userRec.net / userRec.liab)
          , items = [{net:userRec.net, color}]
        arcs = this.gen.pieGen(items)			//Generate net-worth circle
      } else if (tag == 'al') {
        let items = [{net:userRec.liab, color:'red'}, {net:userRec.asset, color:'blue'}]
        arcs = this.gen.pieGen(items)			//Generate assets/liabilities ring
      } else if (tag == 'ch') {
        arcs = this.gen.pieGen(userRec.tallies)	//Generate outer CHIP ring
        radius = oRad					//Remember outer radius
      }
      arcs.forEach(arc => {
        let d = arc.data
          , pathData = pathGen(arc)
        d.cent = tag == 'nw' ? [0,0] :  pathGen.centroid(arc)	//Save centroid for placement algorithm
//console.log("A", i, tag, arc, d)
        d.hub = {					//Connection point
          a: (arc.startAngle + arc.endAngle - Math.PI) / 2,
          r: radius
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
        <text x="${-radius}" y="${-radius -this.fontSize/2}" style="font:normal ${this.fontSize}px sans-serif";>
          ${userRec.peer_cid}:${userRec.peer_agent.slice(-truncAgent)}
        </text>
        ${textCmds.join('\n')}
      </g>`
//console.log("User body:", body, width, height)
    return {state: {body, radius}, lookup, inside: true, latest}
  }
  
  peer(part, user, tally) {			//Generate SVG code for a peer node
    let [ cid, agent ] = part.split(':')
      , xOff = this.fontSize / 2
      , yOff = this.fontSize + 3
      , max = Math.max(cid.length + 2, agent.length + 6)	//take tspan into account
      , width = max * this.fontSize * 0.5,	w2 = width / 2
      , height = this.fontSize * 4,		h2 = height / 2
      , radius = w2
      , text = `
      <text x="${xOff}" y="${yOff}" style="font:normal ${this.fontSize}px sans-serif;">
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
