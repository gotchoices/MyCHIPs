//Admin interface; User Relationship Network Graph
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
// TODO:
//X- Update tally totals when chits added, removed
//X- Update tallies when added, removed
//X- updateNodes() can't handle a deleted node, can only add them
//X- When we get a notice from the database, only load those nodes, tallies that have changed
//X- Make totals reactive, auto update when sums come in
//X- Tallies disappear if I delete them
//X- Hubs collapse down if I remove a tally under the stack
//- 

<template>
  <div>
    <div class="header">User Relation Network Graph:</div>
    <wylib-svgraph :state="state" ref="svg" @refresh="refresh" @reset="reset"/>
  </div>
</template>

<script>
import Wylib from 'wylib'
const Bias = 10				//Amount to nudge nodes based on which end of the tally they are on
const CHIPmult = 1000
var updatePending = false

export default {
  name: 'app-urnet',
  components: {'wylib-svgraph': Wylib.SvGraph},
  props: {
    state:	{type: Object, default: ()=>({})},
  },
  inject: ['top'],			//Where to send modal messages
  data() { return {
    tabGap:	40,
    fontSize:	16,
    hubWidth:	100,
    hubHeight:	20,
    tallies:	{},
    stateTpt:	{nodes:{}},
  }},
  computed: {
    totals: function() {
//console.log("Totals:", Object.keys(this.tallies).length)
      let tots = {}
      Object.keys(this.tallies).forEach(key=>{
        let debits = 0, credits = 0
        this.tallies[key].stock.forEach(st=>{debits += st})
        this.tallies[key].foil.forEach(fo=>{credits += fo})
        tots[key] = {debits, credits}
      })
      return tots
    },
  },
  methods: {
    peer(dat) {				//Generate SVG code for a user/peer node
//console.log("User", dat.id, dat.peer_cid, this.unitss[dat.peer_cid])
      let { id, std_name, peer_cid, peer_sock, user_ent } = dat
        , fColor = (dat.units < 0 ? '#ff0000' : '#0000ff')
        , sumLine = user_ent ? `${dat.stock_uni/CHIPmult} - ${-dat.foil_uni/CHIPmult} = <tspan stroke="${fColor}" fill="${fColor}">${(dat.units/CHIPmult)}</tspan>` : ''
        , yOff = this.fontSize + 3
        , host = peer_sock.split('.')[0]
        , cidLine = `${peer_cid}@${host}`
        , text = `
        <text x="4" y="${yOff}" style="font:normal ${this.fontSize}px sans-serif;">
          ${id}:${std_name}
          <tspan x="4" y="${yOff * 2}">${cidLine}</tspan>
          <tspan x="4" y="${yOff * 3}">${sumLine}</tspan>
        </text>`
        , max = Math.max(cidLine.length + 2, std_name.length + 6, sumLine.length-48)	//take tspan into account
        , width = max * this.fontSize * 0.55
        , height = this.fontSize * 3.8
        , bColor = user_ent ? "#d0d0e4" : "#d0e4d0"
        , body = `
        <g stroke="black" stroke-width="1">
          <rect rx="4" ry="4" width="${width}" height="${height}" fill="${bColor}"/>
          ${text}
        </g>`
        , ends = [{x:width/2, y:0}, {x:width, y:height*0.5}, {x:width/2, y:height}, {x:0, y:height*0.5}]
//console.log("User body:", body, width, height)
      return {body, ends, width, height}
    },

    updateLink(i, idx, cid, dat) {
      let node = this.state.nodes[cid]					//Get node's state object
        , uuid = dat.uuids[i]
        , isFoil = (dat.types[i] == 'foil')
        , amount = dat.unitss[i] / CHIPmult
        , link = dat.part_cids[i]		//Which other node this link is pointing to
        , inside = dat.insides[i]		//Native or foreign user
        , noDraw = (isFoil && inside)
        , reverse = (isFoil && !inside)
        , nodeLink = node.links.find(lk => (lk.index == uuid))	//Do we already have a definition for this link?
        , xOffset = node.width / 2
        , yOffset = isFoil ? node.height + (this.hubHeight * (idx + 0.5)) : -this.hubHeight * (idx + 0.5)	//Stack it on top (stocks) or on bottom (foils)
        , hubColor = amount == 0 ? '#f0f0f0' : (amount < 0 ? '#F0B0B0' : '#B0B0F0')
        , color = dat.states[i] == 'open' ? 'blue' : 'orange'
        , hubYRad = this.hubHeight/2, hubXRad = this.hubWidth/2
        , ends = [{x:xOffset-hubXRad, y:yOffset}, {x:xOffset+hubXRad, y:yOffset}]
        , center = {x:xOffset, y:yOffset}

      if (!nodeLink) {				//Create new data structure for link, hubs
        nodeLink = {index:uuid, link, ends, color, center, noDraw:null, reverse:null, found:true, hub:null, bias:null}
        node.links.push(nodeLink)
      }
//console.log("  link:", link, node, 'idx:', idx, cid, amount, yOffset, nodeLink)
      Object.assign(nodeLink, {ends, center, color, link, noDraw, reverse, found:true, bias: ()=>{
//console.log("User bias:", cid, isFoil, isFoil?-Bias:Bias)
        return {x:0, y: isFoil ? -Bias : Bias}
      }, hub: ()=>{
        return `<g transform="translate(${center.x}, ${center.y})">
          <ellipse rx="${hubXRad}" ry="${hubYRad}" stroke="black" stroke-width="1" fill="${hubColor}"/>
          <text y="${hubYRad/2}" text-anchor="middle" style="font:normal ${this.fontSize}px sans-serif;">${amount}</text>
        </g>`
      }})
    },

    updateNodes(dTime) {
      let where = [['peer_ent', 'notnull']]
        , fields = ['id', 'std_name', 'peer_cid', 'peer_sock', 'user_ent', 'units', 'stock_uni', 'foil_uni', 'tallies', 'types', 'unitss', 'states', 'uuids', 'part_cids', 'insides']
        , spec = {view: 'mychips.users_v_tallysum', fields, where, order: 1}
      updatePending = true
      if (dTime) where.push(['latest', '>=', dTime])
//console.log("UN:", dTime, typeof dTime, where)

      Wylib.Wyseman.request('urnet.peer.'+this._uid, 'select', spec, (data,err) => {
        updatePending = false
        let notFound = Object.assign({}, this.state.nodes)	//Track any nodes on our graph but no longer returned in the query
          , needLinks = {}
//console.log("Update nodes:", dTime, this.state.nodes, data.length, data)
        for (let d of data) {					//For each node
          let bodyObj = this.peer(d)				//Build its SVG shape
            , radius = bodyObj.width / 2			//Radius for use in repel forces
            , cid = d.peer_cid
          if (cid in this.state.nodes) {			//If we already have this node on the graph
            Object.assign(this.state.nodes[cid], bodyObj, {radius})	//Repaint the body
//console.log("n Dat:", cid, this.state.nodes[cid])
          } else {						//Else put it somewhere random on the graph
            let x = Math.random() * this.state.maxX * 0.9
              , y = Math.random() * this.state.maxY * 0.9
            this.$set(this.state.nodes, cid, Object.assign(bodyObj, {tag:cid, x, y, radius, links:[]}))
//console.log("N Dat:", cid, x, y)
          }
//console.log("Dat:", d)
          let stocks = 0, foils = 0
          for (let i = 0; i < d.tallies; i++) {			//Now go through this node's tallies
            let idx = (d.types[i] == 'stock') ? stocks++ : foils++
            this.updateLink(i, idx, cid, d)
            if (!d.insides[i]) {			//Foreign peers don't have tallies, we need to link them in
              let pcid = d.part_cids[i]
                , pnode = this.state.nodes[pcid]
//console.log("Need to link:", cid, "to:", pcid, pnode)
              if (!(pcid in needLinks)) needLinks[pcid] = []
              needLinks[pcid].push({link: cid, noDraw: true, bias: ()=>{
//console.log("Foreign bias:", pcid, d.types[i], d.types[i]=='stock'?-Bias:Bias)
                return {x:0, y:d.types[i] == 'stock' ? -Bias : Bias}
              }})
            }
          }
          let node = this.state.nodes[cid]
          for (let i = node.links.length - 1; i >= 0; i--) {
            let link = node.links[i]
//console.log("  checking:", i, link, link.found)
            if (!dTime && !link.found) node.links.splice(i,1)	//Delete if not found this iteration
            link.found = false
          }
          delete notFound[cid]					//Note we processed this node
        }
//console.log("Not found:", notFound, this.state.nodes)
        if (!dTime) Object.keys(notFound).forEach(key=>{	//Delete anything on the SVG, not now in nodes
          this.$delete(this.state.nodes, key)
        })
//console.log("Need Links:", needLinks)
        Object.keys(needLinks).forEach(key=>{
          let node = this.state.nodes[key]
          if (node) node.links = needLinks[key]
        })
      })
    },		//updateNodes

    refresh() {			//Readjust to any new nodes
      this.updateNodes()
    },
    reset() {			//Start over with random placement
      this.state.nodes = {}
      this.updateNodes()
      this.updateNodes()
//      this.$nextTick(()=>{
//        this.$refs.svg.$emit('bump')
//      })
    },
  },

  beforeMount: function() {
    Wylib.Common.stateCheck(this)
    
    Wylib.Wyseman.listen('urnet.async.'+this._uid, 'mychips_admin', dat => {
//      let dTime = updatePending || dat.oper == 'DELETE' ? null : dat.time	//Only query late changing entries
//console.log("URnet async:", dat, dat.oper == 'DELETE', updatePending, dTime)

      if (dat.target == 'peers' || dat.target == 'tallies')
        this.updateNodes(dat.oper == 'DELETE' ? null : dat.time)
//        this.updateNodes(dTime)		//Disable 01-May-2020 patch for now as it messes up screen redraws

      if (dat.oper == 'DELETE' || dat.oper == 'INSERT')
        this.$refs.svg.$emit('change')		//Automatic bump each time something changes
    })
  },

  mounted: function() {
    this.updateNodes()
  }
}
</script>
