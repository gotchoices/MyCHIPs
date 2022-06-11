//Admin interface; User Relationship Network Graph
//This version deprecated
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
// TODO:
//- 

<template>
  <div>
    <div class="header">User Relation Network Graph:</div>
    <wylib-svgraph1 :state="state" ref="svg" @refresh="refresh" @reset="reset"/>
  </div>
</template>

<script>
import Wylib from 'wylib'
const Bias = 10				//Amount to nudge nodes based on which end of the tally they are on
const CHIPmult = 1000
var updatePending = false

export default {
  name: 'app-urnet',
  components: {'wylib-svgraph1': Wylib.SvGraph1},
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
    user(dat) {				//Generate SVG code for a user node
//console.log("User", dat.id, dat.peer_cid, this.unitss[dat.peer_cid])
      let { id, std_name, peer_cid, peer_agent } = dat
        , fColor = (dat.net < 0 ? '#ff0000' : '#0000ff')
        , sumLine = `${dat.stock_uni/CHIPmult} + ${-dat.foil_uni/CHIPmult} = <tspan stroke="${fColor}" fill="${fColor}">${(dat.net/CHIPmult)}</tspan>`
        , yOff = this.fontSize + 3
        , cidLine = `${peer_cid}:${peer_agent}`
        , text = `
        <text x="4" y="${yOff}" style="font:normal ${this.fontSize}px sans-serif;">
          ${id}:${std_name}
          <tspan x="4" y="${yOff * 2}">${cidLine}</tspan>
          <tspan x="4" y="${yOff * 3}">${sumLine}</tspan>
        </text>`
        , max = Math.max(cidLine.length + 2, std_name.length + 6, sumLine.length-48)	//take tspan into account
        , width = max * this.fontSize * 0.55
        , height = this.fontSize * 3.8
        , bColor = "#d0d0e4"
        , body = `
        <g stroke="black" stroke-width="1">
          <rect rx="4" ry="4" width="${width}" height="${height}" fill="${bColor}"/>
          ${text}
        </g>`
        , ends = [{x:width/2, y:0}, {x:width, y:height*0.5}, {x:width/2, y:height}, {x:0, y:height*0.5}]
//console.log("User body:", body, width, height)
      return {body, ends, width, height}
    },

    peer(dat, i) {				//Generate SVG code for a peer node
//console.log("Peer", dat, i, dat.part_cids[i])
      let cid = dat.part_cids[i]
        , agent = dat.part_agents[i]
        , bColor = "#d0e4d0"
        , yOff = this.fontSize + 3
        , cidLine = `${cid}:${agent}`
        , text = `
        <text x="4" y="${yOff}" style="font:normal ${this.fontSize}px sans-serif;">
          ${cid}:
          <tspan x="4" y="${yOff * 2}">${agent}</tspan>
        </text>`
        , max = Math.max(cid.length + 2, agent.length + 6)	//take tspan into account
        , width = max * this.fontSize * 0.55
        , height = this.fontSize * 2.8
        , body = `
        <g stroke="black" stroke-width="1">
          <rect rx="4" ry="4" width="${width}" height="${height}" fill="${bColor}"/>
          ${text}
        </g>`
//        , body = `
//        <g stroke="black" stroke-width="1">
//          <ellipse cx="${width/2}" cy="${height/2}" rx="${width/2}" ry="${height/2}" stroke="black" stroke-width="1" fill="${bColor}"/>
//          ${text}
//        </g>`
        , ends = [{x:width/2, y:0}, {x:width, y:height*0.5}, {x:width/2, y:height}, {x:0, y:height*0.5}]
//console.log("Peer ends", ends)
      return {body, ends, width, height}
    },

    updateLink(i, idx, cid, dat) {
      let node = this.state.nodes[cid]				//Get node's state object
        , uuid = dat.uuids[i]
        , isFoil = (dat.types[i] == 'foil')
        , amount = dat.nets[i] / CHIPmult
        , link = dat.part_cids[i]		//Which other node this link is pointing to
        , linkAgent = dat.part_agents[i]
        , linkEntity = dat.part_ents[i]
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
        , forCid

//Kludgey instantiation of foreign peer copied from updateNodes:
      if (!linkEntity) {				//Tally links to a foreign peer
        let bodyObj = this.peer(dat, i)			//Build its SVG shape
          , radius = bodyObj.width / 2			//Radius for use in repel forces
        forCid = link
        if (forCid in this.state.nodes) {		//If we already have this node on the graph
          Object.assign(this.state.nodes[forCid], bodyObj, {radius})	//Repaint the body
//console.log("Pn Dat:", forCid, this.state.nodes[forCid])
        } else {						//Else put it somewhere random on the graph
          let x = Math.random() * this.state.maxX * 0.9
            , y = Math.random() * this.state.maxY * 0.9
          this.$set(this.state.nodes, forCid, Object.assign(bodyObj, {tag:forCid, x, y, radius, links:[]}))
//console.log("PN Dat:", forCid, x, y)
        }
      }

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
      return forCid
    },

    updateNodes(dTime) {
      let where = [['user_ent', 'notnull']]
        , fields = ['id', 'std_name', 'peer_cid', 'peer_agent', 'user_ent', 'units', 'net', 'stock_uni', 'foil_uni', 'tallies', 'types', 'unitss', 'nets', 'states', 'uuids', 'part_ents', 'part_cids', 'part_agents', 'insides']
        , spec = {view: 'mychips.users_v_tallysum', fields, where, order: 1}
      updatePending = true
      if (dTime) where.push(['latest', '>=', dTime])
//console.log("UN:", dTime, typeof dTime, where)

      Wylib.Wyseman.request('urnet.peer.'+this._uid, 'select', spec, (data,err) => {
        updatePending = false
        let notFound = Object.assign({}, this.state.nodes)	//Track any nodes on our graph but no longer returned in the query
          , needLinks = {}
console.log("Update nodes:", dTime, this.state.nodes, data.length, data)
        for (let d of data) {					//For each user node
          let bodyObj = this.user(d)				//Build its SVG shape
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
          for (let i = 0; i < d.tallies; i++) {		//Now go through this node's tallies
            let idx = (d.types[i] == 'stock') ? stocks++ : foils++
              , forCid = this.updateLink(i, idx, cid, d)
//console.log("forCid:", forCid)
            if (forCid) delete notFound[forCid]
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
console.log("URnet async:", dat, dat.oper)

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
