//Admin interface; User Relationship Network Graph
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
// TODO:
//X- Update tally totals when chits added, removed
//X- Update tallies when added, removed
//X- updateNodes() can't handle a deleted node, can only add them
//- Make more reactive, less query driven
//- When we get a notice from the database, only load those nodes, tallies that have changed
//- Only repaint the nodes that have changed.  Are we rendering the whole page each time?
//- 

<template>
  <div>
    <div class="header">User Relation Network Graph:</div>
    <wylib-svgraph :state="state" ref="svg" @refresh="refresh" @reset="reset"/>
  </div>
</template>

<script>
import Wylib from 'wylib'

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
    stateTpt:	{width: 600, height: 600, nodes:{}},
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
    user(id, name, cdi) {		//Generate SVG code for a user node
//console.log("User", id, cdi, this.totals[cdi])
      let tots = cdi in this.totals ? this.totals[cdi] : {}
        , debits = Math.round(tots.debits || 0)
        , credits = Math.round(-tots.credits || 0)
        , total =  Math.round(debits - credits)
        , fColor = (total < 0 ? '#ff0000' : '#0000ff')
        , sumLine = `${debits} - ${credits} = <tspan stroke="${fColor}" fill="${fColor}">${total}</tspan>`
        , yOff = this.fontSize + 3
        , text = `
        <text x="4" y="${yOff}" style="font:normal ${this.fontSize}px sans-serif;">
          ${id}:${name}
          <tspan x="4" y="${yOff * 2}">${cdi}</tspan>
          <tspan x="4" y="${yOff * 3}">${sumLine}</tspan>
        </text>`
        , max = Math.max(cdi.length, name.length + 6, sumLine.length-44)	//take tspan into account
        , width = max * this.fontSize * 0.55
        , height = this.fontSize * 3.8
        , body = `
        <g stroke="black" stroke-width="1">
          <rect rx="4" ry="4" width="${width}" height="${height}" fill="#e0e0e0"/>
          ${text}
        </g>`
        , ends = [{x:width/2, y:0}, {x:width, y:height*0.5}, {x:width/2, y:height}, {x:0, y:height*0.5}]
//console.log("User body:", width, height)
      return {body, ends, width, height}
    },

    updateNodes() {
      let spec = {view: 'mychips.users_v', fields: ['id', 'std_name', 'peer_cdi'], where: [['id', '>', '1']], order: 1}
      Wylib.Wyseman.request('urnet.user.'+this._uid, 'select', spec, (data,err) => {
        let notFound = Object.assign({}, this.state.nodes)
//console.log("Update nodes")
        for (const dat of data) {
          let bodyObj = this.user(dat.id, dat.std_name, dat.peer_cdi)
            , radius = bodyObj.height / 2
          if (dat.peer_cdi in this.state.nodes) {
            Object.assign(this.state.nodes[dat.peer_cdi], bodyObj, {radius})
//console.log("n Dat:", dat.peer_cdi, this.state.nodes[dat.peer_cdi].body)
          } else {
            let x = Math.random() * this.state.width/2
              , y = Math.random() * this.state.height/2
            this.$set(this.state.nodes, dat.peer_cdi, Object.assign(bodyObj, {tag:dat.peer_cdi, x, y, radius, links:[]}))
//console.log("N Dat:", dat.peer_cdi, nodeState.x, nodeState.y, this.state.nodes[dat.peer_cdi].x)
          }
          delete notFound[dat.peer_cdi]
        }
//console.log("Not found:", notFound, this.state.nodes)
        Object.keys(notFound).forEach(key=>{			//Delete anything on the SVG, not now in nodes
          this.$delete(this.state.nodes, key)
        })
      })
    },		//updateNodes

    updateLinks() {
      let spec = {view: 'mychips.tallies_v', fields: ['tally_ent', 'tally_seq', 'tally_guid', 'tally_type', 'user_cdi', 'part_cdi', 'total_c'], where: {state: 'open'}, order: [1,2]}
      Wylib.Wyseman.request('urnet.tally.'+this._uid, 'select', spec, (data, err) => {
        if (err || !data) return
        let haveHubs = {}					//Keep track of hub stacking
        for (const dat of data) {				//For each tally link
//console.log("L Dat:", dat)

          let node = this.state.nodes[dat.user_cdi]		//Get node's state
            , nodeLink = node.links.find(link => {return link.index == dat.tally_guid})	//Do we already have a definition for this link?
            , idx = (tag => {					//Calculate an order 0..n for hub stacking
                if (tag in haveHubs) {return (haveHubs[tag] += 1)} else {return (haveHubs[tag] = 0)}
              })(node.tag + dat.tally_type)
            , isFoil = (dat.tally_type == 'foil')
            , xOffset = node.width / 2
            , yOffset = isFoil ? node.height + (this.hubHeight * (idx + 0.5)) : -this.hubHeight * (idx + 0.5)	//Stack it on top (stocks) or on bottom (foils)
            , color = dat.total_c == 0 ? '#f0f0f0' : (dat.total_c < 0 ? '#F0B0B0' : '#B0B0F0')
            , hubYRad = this.hubHeight/2, hubXRad = this.hubWidth/2
            , ends = [{x:xOffset-hubXRad, y:yOffset}, {x:xOffset+hubXRad, y:yOffset}]
            , center = {x:xOffset, y:yOffset}

          if (!(dat.user_cdi in this.tallies)) this.$set(this.tallies,dat.user_cdi,{stock:[], foil:[]})
          this.tallies[dat.user_cdi][dat.tally_type].splice(idx,1,dat.total_c)
//console.log('Add to tallies')
          if (!nodeLink) {				//Create new data structure for link, hubs
            nodeLink = {index:dat.tally_guid, link:dat.part_cdi, draw:isFoil, ends, center, hub:null}
            node.links.push(nodeLink)
          }
//console.log("  node:", node, idx, dat.user_cdi, dat.part_cdi, nodeLink)
          Object.assign(nodeLink, {ends, center, found:true, hub: ()=>{
            return `<g transform="translate(${center.x}, ${center.y})">
              <ellipse rx="${hubXRad}" ry="${hubYRad}" stroke="black" stroke-width="1" fill="${color}"/>
              <text y="${hubYRad/2}" text-anchor="middle" style="font:normal ${this.fontSize}px sans-serif;">${dat.total_c}</text>
            </g>`
          }})
        }	//for-i
        Object.values(this.state.nodes).forEach(node=>{		//Locate any tallies on the SVG, no longer in the DB
          if (node.links) node.links.forEach((link,idx)=>{
            if (!link.found) {node.links.splice(idx,1)}		//If not marked in previous iteration
            link.found = false
          })
        })
      })	//request
    },		//updateLinks

    refresh() {
      this.updateLinks()
      this.updateNodes()
    },
    reset() {
      this.state.nodes = {}
      this.refresh();
    },
  },

//  created: function() {
//    this.updateNodes()
//    this.updateLinks()
//  },
  beforeMount: function() {
    Wylib.Common.stateCheck(this)
    
    this.updateNodes()
    this.updateLinks()
    Wylib.Wyseman.listen('urnet.async.'+this._uid, 'mychips_admin', dat => {
//console.log("Async:", dat)
      if (dat.target == 'peers') this.updateNodes()
      if (dat.target == 'chits' || dat.target == 'tallies') this.refresh()
    })
  }
}
</script>
