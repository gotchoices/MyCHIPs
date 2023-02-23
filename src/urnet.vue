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
const d3 = require('d3')
const { VisBSInit, VisBSUser } = require('./visbs.js')
const View = 'mychips.users_v_tallies'

export default {
  name: 'app-urnet2',
  components: {'wylib-svgraph': Wylib.SvGraph},
  props: {
    state:	{type: Object, default: ()=>({})},
    env:	{type: Object, default: {}}
  },
  inject: ['top'],			//Where to send modal messages
  data() { return {
    viewMeta:	null,
    nodeData:	{},
    stateTpt:	{nodes:{}, edges:{}},
    userRadius:	null,
    simulation:	null,			//Simulation object
  }},

  computed: {
    menu() {return [
      {tag: 'lenLoc',    min:1,   max:20,   step:0.10,  default:4,     lang: this.viewMeta?.msg?.lenLoc},
      {tag: 'lenFor',    min:1,   max:4,    step:0.10,  default:2,     lang: this.viewMeta?.msg?.lenFor},
      {tag: 'locPull',   min:0,   max:0.25, step:0.001, default:0.005, lang: this.viewMeta?.msg?.locPull},
      {tag: 'forPull',   min:0,   max:0.5,  step:0.01,  default:0.25,  lang: this.viewMeta?.msg?.forPull},
      {tag: 'centPull',  min:0,   max:1,    step:0.05,  default:0.8,   lang: this.viewMeta?.msg?.centPull},
      {tag: 'repel',     min:0,   max:5,    step:0.1,   default:1,     lang: this.viewMeta?.msg?.repel},
      {tag: 'vertAlign', min:0,   max:1,    step:0.05,  default:0.35,  lang: this.viewMeta?.msg?.vertAlign},
      {tag: 'floatSink', min:0,   max:.5,   step:0.01,  default:0.15,  lang: this.viewMeta?.msg?.floatSink},
      {tag: 'simDecay',  min:0.001,max:0.5, step:0.001, default:0.05,  lang: this.viewMeta?.msg?.simDecay},
      {tag: 'velDecay',  min:0,   max:1,    step:0.05,  default:0.3,   lang: this.viewMeta?.msg?.velDecay},
    ]},
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
          return node.state.ends
        }
      }
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
            , edges = []
            , visBSUser = new VisBSUser(user)
            , state = visBSUser.user(user)
            , { latest, lookup } = user
            , userNode = {state, lookup, latest, inside: true}

          this.userRadius = visBSUser.userRadius
          if (tag in nodes && nodes[tag].latest >= user.latest) continue

          if (!(tag in this.nodeData)) this.nodeData[tag] = {}	//Keep structure of all node data
          Object.assign(this.nodeData[tag], user, {tag})

//console.log("  User:", tag, user.tallies)
          for (const tally of user.tallies) {			//Look through user's tallies
//console.log("    tally:", tally)
            let pTag = tally.part
            delete edgeStray[tally.uuid]

            if (tally.part && !tally.inside) {			//Partner is a foreign peer
              pTag = (tally.part + '~' + tally.ent + '-' + tally.seq)
              let state = visBSUser.peer(tally)
                , peer = {state, user: tag, tally, inside: false}
              this.putNode(pTag, peer)
              delete nodeStray[pTag]
            } else if (!(tally.part in nodes)) {		//Local partner not on graph yet
//console.log("ZZZ:", tally.part, Object.keys(this.state.nodes))
              continue						//Wait to process his record
            }
//if (!tag || !pTag) console.log("BAD TAG:", tag, pTag)
            if (!(tally.uuid in this.state.edges)) {
              edges.push(tally.type == 'foil' ?
                {source:{tag}, target:{tag:pTag}, uuid:tally.uuid, inside:tally.inside} :
                {source:{tag:pTag}, target:{tag}, uuid:tally.uuid, inside:tally.inside})
            }
          }

          this.putNode(tag, userNode)		//;console.log("Put:", tag)
          delete nodeStray[tag]
          edges.forEach(edge => {this.$set(this.state.edges, edge.uuid, edge)})
        }

//console.log("Nodes:", this.state.nodes)
//console.log("Will delete:", nodeStray, edgeStray)
        Object.keys(nodeStray).forEach(tag => {		//Delete anything on the SVG, not now in nodes
          this.$delete(this.state.nodes, tag)
          this.$delete(this.nodeData, tag)
        })
        Object.keys(edgeStray).forEach(tag => {		//Same for edges
          this.$delete(this.state.edges, tag)
        })

//console.log("Node Data:", this.nodeData)
        this.simInit()
      })	//WM request
    },		//updateNodes

    simInit(alpha = 1) {
      let nodeList = Object.values(this.nodeData).map(el => (el.state))
        , linkList = Object.values(this.state.edges).map(edge => ({
          source: this.nodeData[edge.source.tag]?.state,
          target: this.nodeData[edge.target.tag]?.state,
          inside:edge.inside
        }))
        , sets = this.state.setting
        , uRad = this.userRadius
//console.log("simInit:", uRad, this.state.edges)

      this.simulation = d3.forceSimulation(nodeList)
        .alpha(alpha).alphaDecay(sets.simDecay || 0.05)
        .velocityDecay(sets.velDecay || 0.03)

      .force('link', d3.forceLink(linkList).distance(d => {
//console.log("LD:", d, typeof d.inside, d.inside ? sets.lenLoc : sets.lenFor)
        return uRad * (d.inside ? sets.lenLoc : sets.lenFor)
      }).strength(d => {
        return ((d.inside ? sets.locPull : sets.forPull) || 0.05)
        sets.linkPull || 0.05
      }))

      .force('center', d3.forceCenter()		//Nodes like the graph center
          .strength(sets.centPull || 0.1))
      
      .force('charge', d3.forceManyBody()	//Nodes repel each other
          .strength(-(sets.repel || 10)))

      .force('x', d3.forceX().strength(
        sets.vertAlign || 0.05
      ).x(d => {		//Align foreign peers with user tally
//console.log('X:', d, this.state)
        let node = this.nodeData[d.tag]				//;console.log('FX:', node)
        if (node.inside) return d.x				//Do nothing for users
        let uNode = this.nodeData[node.user]			//;console.log('FXu:', uNode)
        return (uNode.state.x + node.tally.cent[0])		//peers get pushed to align with user tally
      }))

      .force('collision', d3.forceCollide().strength(0.75).radius(d => {
        return d.radius
      }))

      .force('y', d3.forceY().strength(		//Assets should move up, liabilities move down
        sets.floatSink || 0.2
      ).y(d => {				//Float or sink
        let node = this.nodeData[d.tag]
//console.log('Y:', d, this.state)
        if (node.inside) {			//Local users
          let node = this.nodeData[d.tag]
//console.log('Yl:', node.assets, node.liabs)
          if (node.assets <= 0 || node.liabs <= 0) return 0	//Untethered nodes hang near X axis
          return ((node.assets - node.liabs) * uRad)
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
    VisBSInit({d3})
//console.log("URNet2 beforeMount:", this.state)    

    Wylib.Wyseman.listen('urnet.async.'+this._uid, 'mychips_admin', dat => {
//console.log("URnet async:", dat, dat.oper)

      if (dat.target == 'users' || dat.target == 'tallies')
        this.updateNodes(dat.oper == 'DELETE' ? null : dat.time)
        this.refresh()

//      if (dat.oper == 'DELETE' || dat.oper == 'INSERT')	//Fixme: eliminate this?
//        this.$refs.svg.$emit('change')	//Automatic bump each time something changes
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
