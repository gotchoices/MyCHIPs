//Admin interface; User Relationship Network Graph
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
// TODO:
//- Deal better with restart of simulator (clear out node info caching?)
//- Record last-modified date for each node, only update what has changed (Fixme below)
//- 
<template>
  <div>
    <div class="header">User Relation Network Graph:</div>
    <wylib-svgraph :state="state" :env="env" :curve="true" :edge="edge" :menu="menu" ref="svg"
        @drag="dragHand" @drop="dropHand" @input="restart" @refresh="refresh" @reset="reset">
      <template v-slot:def>
        <radialGradient id="radGrad">
          <stop offset="0%" style="stop-color:#FFF; stop-opacity:0.9"/>
          <stop offset="100%" style="stop-color:#ccc; stop-opacity:0"/>
        </radialGradient>
      </template>
    </wylib-svgraph>
  </div>
</template>

<script>
import Wylib from 'wylib'
//require("regenerator-runtime/runtime")        //Webpack needs this for async/generators (d3)
const D3 = require('d3')
const View = 'mychips.users_v_tallies'
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

export default {
  name: 'app-urnet2',
  components: {'wylib-svgraph': Wylib.SvGraph},
  props: {
    state:	{type: Object, default: ()=>({})},
    env:	{type: Object, default: {}}
  },
  inject: ['top'],			//Where to send modal messages
  data() { return {
    fontSize:	18,
    viewMeta:	null,
    nodeData:	{},
    stateTpt:	{nodes:{}, edges:{}},
    gen:	{},			//holds D3 generators
    simulation:	null,			//Simulation object
    userRadius:	80,
    ringData: [
      {tag: 'nw', rad: 30, title: 'Net Worth'},
      {tag: 'al', rad: 20, title: 'Assets & Liabilities'},
      {tag: 'ch', rad: 30, title: 'CHIP Tallies'}
    ]
  }},

  computed: {
    menu() {return [
      {tag: 'lenLoc', min:1, max:20, step:0.10, default:4, lang: this.viewMsg.lenLoc},
      {tag: 'lenFor', min:1, max:4, step:0.10, default:2, lang: this.viewMsg.lenFor},
      {tag: 'locPull', min:0, max:0.25, step:0.001, default:0.005, lang: this.viewMsg.locPull},
      {tag: 'forPull', min:0, max:0.5, step:0.01, default:0.25, lang: this.viewMsg.forPull},
      {tag: 'centPull', min:0, max:1, step:0.05, default:0.8, lang: this.viewMsg.centPull},
      {tag: 'repel', min:0, max:5, step:0.1, default:1, lang: this.viewMsg.repel},
      {tag: 'vertAlign', min:0, max:1, step:0.05, default:0.35, lang: this.viewMsg.vertAlign},
      {tag: 'floatSink', min:0, max:.5, step:0.01, default:0.15, lang: this.viewMsg.floatSink},
      {tag: 'simDecay', min:0.001, max:0.5, step:0.001, default:0.05, lang: this.viewMsg.simDecay},
      {tag: 'velDecay', min:0, max:1, step:0.05, default:0.3, lang: this.viewMsg.velDecay},
    ]},
    viewMsg() {
      return this.viewMeta ? this.viewMeta.msg : {}
    },
  },

  methods: {
    randPoint() {return {
      x: (Math.random() - 0.5) * (this.state.maxX - this.state.minY) * 0.9,
      y: (Math.random() - 0.5) * (this.state.maxX - this.state.minX) * 0.9
    }},

    edge(thisSide, otherSide, edgeState) {		//Edge requesting endpoint
      let {uuid} = edgeState				//Parts of querying edge
        , node = this.nodeData[thisSide.tag]
//console.log("edge", thisSide, otherSide, node)
      if (node) {
        if (node.inside) {
          let nodeTally = node.lookup[uuid]
          if (nodeTally) return nodeTally.hub
        } else {
          return node.ends
        }
      }
    },

    userSetup(tag, userRec) {			//Generate control object for a user node
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
    },

    peerSetup(part, user, tally) {			//Generate SVG code for a peer node
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
    },

    putNode(tag, node) {			//Add or udpate node info to data structure
      if (tag in this.state.nodes) {			//If we already have this node on the graph
        Object.assign(this.state.nodes[tag], node.state)	//Reassign properties
      } else {					//Make it from scratch with random placement
        this.$set(this.state.nodes, tag, Object.assign(node.state, {tag}, this.randPoint()))
      }
      node.state = this.state.nodes[tag]		//Point to correct/updated state object
      if (!(tag in this.nodeData)) this.nodeData[tag] = {}
      Object.assign(this.nodeData[tag], node)
    },

    updateNodes() {
      let where = [['user_ent', 'notnull']]
        , fields = ['id', 'std_name', 'peer_cid', 'peer_agent', 'asset', 'assets', 'liab', 'liabs', 'net', 'latest', 'tallies']
        , spec = {view: View, fields, where, order: 1}

      Wylib.Wyseman.request('urnet.peer.'+this._uid, 'select', spec, (users, err) => {
        if (err) {console.err('Error:', err.message); return}
        let nodes = this.state.nodes
          , nodeStray = Object.assign({}, nodes)	//Track any nodes on our graph but no longer in the DB
          , edgeStray = Object.assign({}, this.state.edges)
//console.log("Update nodes:", nodes, users.length, users)
   
        for (let user of users) {				//For each user record
          let tag = user.peer_cid + ':' + user.peer_agent
            , shades = {				//Separate gradient for positive/negative
                true:  D3.quantize(this.gen.posChColor, Math.max(2, user.assets)),	//positive
                false: D3.quantize(this.gen.negChColor, Math.max(2, user.liabs))	//negative
              }
            , slice = 0					//Counter for color calculations
            , edges = []

          if (tag in nodes && nodes[tag].latest >= user.latest) continue

          if (!(tag in this.nodeData)) this.nodeData[tag] = {}	//Keep structure of all node data
          Object.assign(this.nodeData[tag], user, {tag})

//console.log("  User:", tag, user.tallies)
          user.lookup = {}
          user.tallies.sort((a,b) => (a.net - b.net))		//DB tally sort has not been dependable
          for (const tally of user.tallies) {			//Look through user's tallies
//console.log("    tally:", tally)
            let pTag = tally.part
              , idx = tally.net >= 0 ? user.tallies.length - (++slice) : slice++
            tally.color = shades[tally.net >= 0][idx]		//Compute slice colors
            user.lookup[tally.uuid] = tally			//tally lookup table by uuid
            delete edgeStray[tally.uuid]

            if (!tally.inside) {				//Partner is a foreign peer
              pTag = (tally.part + '~' + tally.ent + '-' + tally.seq)
              this.putNode(pTag, this.peerSetup(tally.part, tag, tally))
              delete nodeStray[pTag]
            } else if (!(tag in nodes)) {			//Local partner not on graph yet
              continue						//Wait to process his record
            }
            if (!(tally.uuid in this.state.edges)) {
              edges.push(tally.type == 'foil' ?
                {source:{tag}, target:{tag:pTag}, uuid:tally.uuid, inside:tally.inside} :
                {source:{tag:pTag}, target:{tag}, uuid:tally.uuid, inside:tally.inside})
            }
          }

          this.putNode(tag, this.userSetup(tag, user))
          delete nodeStray[tag]
          edges.forEach(edge => {this.$set(this.state.edges, edge.uuid, edge)})
        }

//console.log("Nodes:", this.state.nodes)
console.log("Will delete:", nodeStray, edgeStray)
        Object.keys(nodeStray).forEach(tag => {		//Delete anything on the SVG, not now in nodes
          this.$delete(this.state.nodes, tag)
          this.$delete(this.nodeData, tag)
        })
        Object.keys(edgeStray).forEach(tag => {		//Same for edges
          this.$delete(this.state.edges, tag)
        })
        this.simInit()
      })	//WM request
    },		//updateNodes

    simInit(alpha = 1) {
      let nodeList = Object.values(this.nodeData).map(el => (el.state))
        , linkList = Object.values(this.state.edges).map(edge => ({
          source: this.nodeData[edge.source.tag].state,
          target: this.nodeData[edge.target.tag].state,
          inside:edge.inside
        }))
        , sets = this.state.setting

      this.simulation = D3.forceSimulation(nodeList)
        .alpha(alpha).alphaDecay(sets.simDecay || 0.05)
        .velocityDecay(sets.velDecay || 0.03)

      .force('link', D3.forceLink(linkList).distance(d => {
//console.log("LD:", d, typeof d.inside, d.inside ? sets.lenLoc : sets.lenFor)
        return this.userRadius * (d.inside ? sets.lenLoc : sets.lenFor)
      }).strength(d => {
        return ((d.inside ? sets.locPull : sets.forPull) || 0.05)
        sets.linkPull || 0.05
      }))

      .force('center', D3.forceCenter()		//Nodes like the graph center
          .strength(sets.centPull || 0.1))
      
      .force('charge', D3.forceManyBody()	//Nodes repel each other
          .strength(-(sets.repel || 10)))

      .force('x', D3.forceX().strength(
        sets.vertAlign || 0.05
      ).x(d => {		//Align foreign peers with user tally
//console.log('X:', d, this.state)
        let node = this.nodeData[d.tag]				//;console.log('FX:', node)
        if (node.inside) return d.x				//Do nothing for users
        let uNode = this.nodeData[node.user]			//;console.log('FXu:', uNode)
        return (uNode.state.x + node.tally.cent[0])		//peers get pushed to align with user tally
      }))

      .force('collision', D3.forceCollide().strength(0.75).radius(d => {
        return d.radius
      }))

      .force('y', D3.forceY().strength(			//Assets should move up, liabilities move down
        sets.floatSink || 0.2
      ).y(d => {		//Float or sink
        let node = this.nodeData[d.tag]
//console.log('Y:', d, this.state)
        if (node.inside) {				//Local users
          let node = this.nodeData[d.tag]
//console.log('Yl:', node.assets, node.liabs)
          if (node.assets <= 0 || node.liabs <= 0) return 0	//Untethered nodes hang near X axis
          return ((node.assets - node.liabs) * this.userRadius)
        } else {					//Foreign peers
          return node.tally.net >= 0 ? this.state.minY : this.state.maxY	//Seek top or bottom of graph
        }
      }))

//      .on('tick', () => {console.log('ticked')})
    },		//simInit

    dragHand(ev, state) {		//When a node is dragged
//console.log("moveHand:", ev.button, ev)
      state.fx = state.x		//Stick nodes in place when dragged
      state.fy = state.y
      this.restart()
    },

    dropHand(ev, state) {		//At the end of a drag
//console.log("dropHand:", ev.button, ev)
      if (!ev.shiftKey) {		//Shift key sticks the node in place
        state.fx = null			//Otherwise they get moved again
        state.fy = null
      }
    },

    restart(ev, state) {		//Start simulation again
//console.log("Restart:", ev, state)
//      if (this.simulation) this.simulation.alpha(1).restart()
      this.simInit()
    },

    refresh() {			//Readjust to any new nodes
      this.updateNodes()
      this.simInit()
    },

    reset() {			//Start over with random placement
      this.state.nodes = {}
      this.state.edges = {}
      this.refresh()
    },
  },

  beforeMount: function() {
    Wylib.Common.stateCheck(this)
//console.log("URNet2 beforeMount:", this.state)    

    let lastRad = 0
    for (let i = 0; i < this.ringData.length; i++) {	//Initialize pie/ring data
      let ring = this.ringData[i]
//console.log("ring:", i, ring)
      ring.iRad = lastRad
      lastRad = ring.oRad = lastRad + ring.rad
      ring.pathGen = D3.arc()			//Generates pie-chart sections
        .cornerRadius(3).innerRadius(ring.iRad).outerRadius(ring.oRad)
    }
    this.userRadius = lastRad
    this.gen.pieGen = D3.pie()			//Pie-chart angle generator
      .startAngle(startAngle).endAngle(endAngle).padAngle(gapAngle)
      .sort(null)				//Already sorted
      .value(d => Math.abs(d.net))
    this.gen.posNwColor = D3.interpolate(neutral, maxNwColor)	//Pie slice color tables
    this.gen.negNwColor = D3.interpolate(neutral, minNwColor)
    this.gen.posChColor = D3.interpolate(maxChipP, minChipP)	//Backwards to accommodate reverse index
    this.gen.negChColor = D3.interpolate(maxChipN, minChipN)
    
    Wylib.Wyseman.listen('urnet.async.'+this._uid, 'mychips_admin', dat => {
//console.log("URnet async:", dat, dat.oper)

      if (dat.target == 'users' || dat.target == 'tallies')
        this.updateNodes(dat.oper == 'DELETE' ? null : dat.time)
        this.refresh()

//Fixme: eliminate?
//      if (dat.oper == 'DELETE' || dat.oper == 'INSERT')
//        this.$refs.svg.$emit('change')		//Automatic bump each time something changes
    })
    
    Wylib.Wyseman.register(this.id+'vm', View, (data, err) => {
      if (err) {console.log(err.msg); return}
      this.viewMeta = data
//console.log("Got meta:", View, this.viewMsg)
    })
  },

  mounted: function() {
    this.updateNodes()
  }
}
</script>
