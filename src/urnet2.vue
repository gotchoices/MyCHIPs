//Admin interface; User Relationship Network Graph
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
// TODO:
//X- Implement visbs.vue as body of svgnode
//X- Each user is a visual balance balance real-time pie-chart
//X- Use constant update d3 or similar to place nodes on chart
//X- Arrows are separate objects--not belonging directly to nodes
//- Fetch language info from data dictionary
//- Create view that's better/more-efficient than users_v_tallysum?
//- Record last-modified date for each node, only update what has changed
//- Search/fix Fixmes below
//- 
//Immediate:
//- Update edge ends on first paint
//- Auto-generate aim points on connectors (optionally)
//- After d3 gravity working, can we remove some of the properties of user/peer? (width,height)
//- Maybe d3/gravity algo should not be in wylib at all (but rather the client app)
//- 
//X- Render foreign peer body
//X-   Provides connector hub coordinates and vector
//-   Has a color to match pie chart slice
//-   Shows tally sum
//- 
//- Local User body
//-   Place tally sum over pie section (only if big enough)
//-   Place sums for assets, liabilities, net-total
//-   Place CHIP Address near body
//-   Hover shows full name and user ID
//-   
//- Optimize/clean code to create user body
//- Optimize/clean code to create peer body
//- Only call body generation code if something has changed since last query (latest)
//- 
//- Convert svgraph2 to use d3-force
//X-   Supply node array to simulation
//X-   Capture tick event (only useful for debugging)
//X-   Update translation x,y in tick handler (done automatically)
//-   Graph bottom border expands to fit view window
//-   D3 exists only in Wylib--invoked/included from there, not in MyCHIPs dir
//- 
//- Forces:
//-   Peers sink or float depending on asset/liability
//-   Peers like to be vertically aligned with associated user pie segment
//-   Internal tallies push neighbor up/down based on asset/liability
//-   Connectors apply attractive force
//-   Nodes repulse each other
//-   Nodes restricted to graph borders
//- 
//- 
//- 

<template>
  <div>
    <div class="header">User Relation Network Graph:</div>
    <wylib-svgraph2 :state="state" :node="node" :edge="edge" ref="svg" @refresh="refresh" @reset="reset">
      <template v-slot:def>
        <radialGradient id="radGrad">
          <stop offset="0%" style="stop-color:#FFF; stop-opacity:0.75"/>
          <stop offset="1000%" style="stop-color:#000; stop-opacity:0.0"/>
        </radialGradient>
      </template>
    </wylib-svgraph2>
  </div>
</template>

<script>
import Wylib from 'wylib'
//require("regenerator-runtime/runtime")        //Webpack needs this for async/generators (d3)
const D3 = require('d3')
const Bias = 10				//Amount to nudge nodes based on which end of the tally they are on

const CHIPmult = 1000
//var updatePending = false

const gapAngle = 0.005			//Gap between slices
const startAngle = Math.PI/2		//Start/end on East axis
const endAngle = Math.PI/2*5

const neutral = '#DDD'			//Halfway between asset and liability
const maxNwColor  = "hsl(230,50%,40%)"	//Positive, assets
const minNwColor  = "hsl(350,50%,40%)"	//Negative, liabilities
const maxChipP = "hsl(200,100%,30%)"	//Darkest positive CHIP
const minChipP = "hsl(200,100%,70%)"	//Lightest positive CHIP
const maxChipN = "hsl(10,100%,30%)"	//Darkest negative CHIP
const minChipN = "hsl(10,100%,70%)"	//Lightest negative CHIP

export default {
  name: 'app-urnet2',
  components: {'wylib-svgraph2': Wylib.SvGraph2},
  props: {
    state:	{type: Object, default: ()=>({})},
  },
  inject: ['top'],			//Where to send modal messages
  data() { return {
    fontSize:	16,
    hubWidth:	100,
    hubHeight:	20,
    tallies:	{},
    stateTpt:	{nodes:{}, edges:{}},
    gen:	{},
    ringData: [
       {tag: 'nw', rad: 30, title: 'Net Worth'}
     , {tag: 'al', rad: 20, title: 'Assets & Liabilities'}
     , {tag: 'ch', rad: 30, title: 'CHIP Tallies'}
    ]
  }},
  computed: {
//    totals: function() {
//console.log("Totals:", Object.keys(this.tallies).length)
//      let tots = {}
//      Object.keys(this.tallies).forEach(key=>{
//        let debits = 0, credits = 0
//        this.tallies[key].stock.forEach(st=>{debits += st})
//        this.tallies[key].foil.forEach(fo=>{credits += fo})
//        tots[key] = {debits, credits}
//      })
//      return tots
//    },
  },
  methods: {
    randPoint() {return {
      x: Math.random() * this.state.maxX * 0.9,
      y: Math.random() * this.state.maxX * 0.9
    }},

    node(state, cmd) {					//Custom service routine
//console.log("Node query", cmd, state)
      return {}
    },

    edge(state, cmd, nodeCenter) {			//Custom service routine
      let {source, target, uuid} = state			//Parts of querying edge
        , tally = this.tallies[uuid]
        , sNode = this.state.nodes[source]
        , tNode = this.state.nodes[target]
//console.log("Edge query", cmd, uuid, tally, sNode, tNode)
      if (cmd == 'source')
        return sNode.local ? tally.hub : sNode.ends
      if (cmd == 'target')
        return tNode.local ? tally.hub : tNode.ends
    },

    userBody(tag, userRec) {			//Generate control object for a user node
console.log("User", tag, userRec.peer_cid, userRec.tallies)
      let { id, std_name, peer_cid, peer_agent, tallies } = userRec
        , paths = []
        , radius
        , fColor = (userRec.net < 0 ? '#ff0000' : '#0000ff')
        , sumLine = `${userRec.asset/CHIPmult} + ${-userRec.liab/CHIPmult} = <tspan stroke="${fColor}" fill="${fColor}">${(userRec.net/CHIPmult)}</tspan>`
        , yOff = this.fontSize + 3
        , cidLine = `${peer_cid}:${peer_agent}`
        , text = `
        <text x="4" y="${yOff}" style="font:normal ${this.fontSize}px sans-serif;">
          ${id}:${std_name}
          <tspan x="4" y="${yOff * 2}">${cidLine}</tspan>
          <tspan x="4" y="${yOff * 3}">${sumLine}</tspan>
        </text>`

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
          d.cent = pathGen.centroid(arc)		//Save centroid for later
          d.hub = {					//Connection point
            a: (arc.startAngle + arc.endAngle - Math.PI) / 2,
            r: radius
          }
//console.log("A", i, tag, arc)
          d.arc = arc					//Access to arc from tally object
          paths.push(`<path d="${pathData}" fill="${d.color}"/>`)
        })
      }
      let width = radius * 2				//Fixme: Still need all these?
        , height = width
//        , ends = [{x:width/2, y:0}, {x:width, y:height*0.5}, {x:width/2, y:height}, {x:0, y:height*0.5}]
        , body = `
        <g stroke="black" stroke-width="0.5">
          ${paths.join('\n')}
          <circle r="${radius}" fill="url(#radGrad)"/>
          ${text}
        </g>`
//console.log("User body:", body, width, height)
      return {body, width, height, radius}
    },

    peerBody(part) {				//Generate SVG code for a peer node
      let [ cid, agent ] = part.split(':')
        , bColor = "#d0e4d0"
        , xOff = this.fontSize / 2
        , yOff = this.fontSize + 3
        , text = `
        <text x="${xOff}" y="${yOff}" style="font:normal ${this.fontSize}px sans-serif;">
          ${cid}:
          <tspan x="${xOff}" y="${yOff * 2}">${agent}</tspan>
        </text>`
        , max = Math.max(cid.length + 2, agent.length + 6)	//take tspan into account
        , width = max * this.fontSize * 0.5
        , height = this.fontSize * 3
        , radius = width / 2
        , body = `
        <g stroke="black" stroke-width="1">
          <rect rx="${yOff}" ry="${yOff}" width="${width}" height="${height}" fill="${bColor}"/>
          <rect rx="${yOff}" ry="${yOff}" width="${width}" height="${height}" fill="url(#radGrad)"/>
          ${text}
        </g>`
        , ends = [{x:width/2, y:0}, {x:width, y:height*0.5}, {x:width/2, y:height}, {x:0, y:height*0.5}]
//console.log("Peer ends", ends)
      return {body, ends, width, height, radius}
    },

    addNode(tag, node) {
      let nodes = this.state.nodes
      if (tag in nodes) {			//If we already have this node on the graph
        Object.assign(nodes[tag], node)		//Reassign properties
      } else {					//Make it from scratch with random placement
        this.$set(nodes, tag, Object.assign(node, {tag}, this.randPoint()))
      }
    },

    updateNodes() {
      let where = [['user_ent', 'notnull']]		//Fixme: simplify/trim query values
        , fields = ['id', 'std_name', 'peer_cid', 'peer_agent', 'asset', 'assets', 'liab', 'liabs', 'net', 'latest', 'tallies']
        , spec = {view: 'mychips.users_v_tallies', fields, where, order: 1}

      Wylib.Wyseman.request('urnet.peer.'+this._uid, 'select', spec, (users, err) => {
        if (err) {console.err('Error:', err.message); return}
        let nodes = this.state.nodes
          , nodeStray = Object.assign({}, nodes)	//Track any nodes on our graph but no longer in the DB
          , edgeStray = Object.assign({}, this.state.edges)
          , userNode = {}, peerNode = {}, edges = []
console.log("Update nodes:", nodes, users.length, users)
   
        for (let user of users) {				//For each user record
          let tag = user.peer_cid + ':' + user.peer_agent
            , slice = 0
            , shades = {				//Separate gradient for positive/negative
              true:  D3.quantize(this.gen.posChColor, Math.max(2, user.assets)),	//positive
              false: D3.quantize(this.gen.negChColor, Math.max(2, user.liabs))		//negative
              }
//Fixme:
//        if (node exists and node.latest >= user.latest) continue

//console.log("  user:", tag)
          for (let tally of user.tallies) {			//Look through user's tallies
//console.log("    tally:", tally)
            let pTag = tally.part
              , idx = tally.net >= 0 ? user.tallies.length - (++slice) : slice++
            tally.color = shades[tally.net >= 0][idx]		//Compute slice colors
            this.tallies[tally.uuid] = tally			//tally lookup table by uuid
            delete edgeStray[tally.uuid]

            if (!tally.inside) {				//Partner is a foreign peer
              pTag = (tally.part + '~' + tally.ent + '-' + tally.seq)
              Object.assign(peerNode, this.peerBody(tally.part), {user:userNode, tally, local:false})
            } else if (!(tag in nodes)) {			//Local partner not on graph yet
              continue						//Wait to process his record
            }
            if (!(tally.uuid in this.state.edges)) {
              edges.push(tally.type == 'foil' ?
                {source:tag, target:pTag, uuid:tally.uuid} :
                {source:pTag, target:tag, uuid:tally.uuid})
            }
            delete nodeStray[pTag]
            this.addNode(pTag, peerNode)
          }

          Object.assign(userNode, this.userBody(tag, user), {local:true})
          delete nodeStray[tag]			//Note we processed this node
          this.addNode(tag, userNode)
          
          for (let edge of edges) {
            this.$set(this.state.edges, edge.uuid, edge)
          }

        }
//Restart simulation
//console.log("Node:", nodes[tag])

        Object.keys(nodeStray).forEach(tag => {		//Delete anything on the SVG, not now in nodes
          this.$delete(this.state.nodes, tag)
        })
        Object.keys(edgeStray).forEach(tag => {		//Delete anything on the SVG, not now in nodes
          this.$delete(this.state.edges, tag)
        })
      })	//WM request
    },		//updateNodes

    simInit(alpha = 1, decay = 0.05) {
      this.simulation = D3.forceSimulation(Object.values(this.state.nodes))
        .alpha(alpha).alphaDecay(decay)
        .velocityDecay(0.3)

//Repel nodes from each other:
      .force('charge', D3.forceManyBody().strength(-100))

//Align foreign peers with user tally
      .force('x', D3.forceX().strength(0.08).x(function(d) {
console.log('FX:', d)
        if (d.local) return d.x				//Do nothing for users
        return (d.user.x + d.tally.cent[0])		//peers get pushed to align with user tally
      }))

//      .force('y', D3.forceY().strength(0.1).y(d => {
//console.log('Y:', height)
//        return (d.holding.asset ? -1 : 1) * (height - ariRad)
//      }))
//      .force('collision', D3.forceCollide().strength(0.75).radius(ariRad))
      .on('tick', () => {
console.log('ticked')
//        paintPartners()
      })
    },		//simInit

    refresh() {			//Readjust to any new nodes
      this.updateNodes()
      this.simInit()
    },

    reset() {			//Start over with random placement
      this.state.nodes = {}
      this.state.edges = {}
//      this.updateNodes()
//      this.updateNodes()
//      this.$nextTick(()=>{
//        this.$refs.svg.$emit('bump')
//      })
    },
  },

  beforeMount: function() {
    Wylib.Common.stateCheck(this)
//console.log("URNet2 beforeMount:", this.state)    

    for (let i = 0, lastRad = 0; i < this.ringData.length; i++) {	//Initialize pie/ring data
      let ring = this.ringData[i]
//console.log("ring:", i, ring)
      ring.iRad = lastRad
      lastRad = ring.oRad = lastRad + ring.rad
      ring.pathGen = D3.arc()			//Generates pie-chart sections
        .cornerRadius(3).innerRadius(ring.iRad).outerRadius(ring.oRad)
    }
    this.gen.pieGen = D3.pie()			//Pie-chart angle generator
      .startAngle(startAngle).endAngle(endAngle).padAngle(gapAngle)
      .sort(null)				//Already sorted
      .value(d => Math.abs(d.net))
    this.gen.posNwColor = D3.interpolate(neutral, maxNwColor)	//Pie slice color tables
    this.gen.negNwColor = D3.interpolate(neutral, minNwColor)
    this.gen.posChColor = D3.interpolate(maxChipP, minChipP)	//Backwards to accommodate reverse index
    this.gen.negChColor = D3.interpolate(maxChipN, minChipN)
    
    Wylib.Wyseman.listen('urnet.async.'+this._uid, 'mychips_admin', dat => {
console.log("URnet async:", dat, dat.oper)

      if (dat.target == 'peers' || dat.target == 'tallies')
        this.updateNodes(dat.oper == 'DELETE' ? null : dat.time)

//Fixme: eliminate?
      if (dat.oper == 'DELETE' || dat.oper == 'INSERT')
        this.$refs.svg.$emit('change')		//Automatic bump each time something changes
    })
  },

  mounted: function() {
    this.state.edges = {}		//Always rebuild edges (with valid term callbacks)
    this.updateNodes()
  }
}
</script>
