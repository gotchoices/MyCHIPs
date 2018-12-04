//Admin interface; User Relationship Network Graph
//Copyright MyCHIPs.org: GNU GPL Ver 3; see: License in root of this package
// -----------------------------------------------------------------------------
// TODO:
//X- Calculate arrows from hub center and end points if hub specified
//X- Can update text in hubs asynchronously
//X- Make database generate notifications when users, totals, tallies changed
//X- Respond to notifications from database
//X- Update nodes when new active user node added
//X- Why don't arrow heads update on hot load?
//X- Update tally totals when chits added, removed
//- Update tallies when added, removed
//- 
//- Later:
//- updateNodes() can't handle a deleted node, can only add them
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
  components: {'wylib-svgraph': Wylib.SvGraph},
  props: {
    state:	{type: Object, default: ()=>({})},
  },
  data() { return {
    tabGap:	40,
    fontSize:	16,
    hubWidth:	100,
    hubHeight:	20,
  }},
  methods: {
    user(id, name, cdi) {		//Generate SVG code for a user node
      let text = `<text x="4" y="${this.fontSize}" style="font:normal ${this.fontSize}px sans-serif;">${id}:${name}<tspan x="4" y="${this.fontSize * 2 + 4}">${cdi}</tspan></text>`
      let max = Math.max(cdi.length, name.length + 6)
      let width = max * this.fontSize * 0.55
        , height = this.fontSize * 3.5
        , code = `
        <g stroke="black" stroke-width="1">
          <rect rx="4" ry="4" width="${width}" height="${height}" fill="#e0e0e0"/>
          ${text}
        </g>`
        , ends = [{x:width/2, y:0}, {x:width, y:height*0.5}, {x:width/2, y:height}, {x:0, y:height*0.5}]
//console.log("Ends:", ends)
      return {code, ends, width, height}
    },

    updateNodes() {
      let spec = {view: 'mychips.users_v', fields: ['id', 'std_name', 'peer_cdi'], where: [['id', '>', '1']], order: 1}
      Wylib.Wyseman.request('urnet.user.'+this._uid, 'select', spec, (data,err) => {
        let notFound = Object.assign({}, this.state.nodes)
        for (const dat of data) {
          if (!(dat.peer_cdi in this.state.nodes)) {
            let { code, ends, width, height } = this.user(dat.id, dat.std_name, dat.peer_cdi)
              , x = Math.random() * this.state.width/2, y = Math.random() * this.state.height/2
              , nodeState = {tag:dat.peer_cdi, x, y, width, height, radius:height/2, code, ends, links:[]}
            this.$set(this.state.nodes, dat.peer_cdi, nodeState)
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
//          if (!(dat.user_cdi in this.state.nodes)) continue	//No matching node found on the graph

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
      this.updateNodes()
      this.updateLinks()
    },
    reset() {
      this.state.nodes = {}
//      Object.keys(this.state.nodes).forEach(key=>{delete this.state.nodes[key]})
      this.refresh();
    },
  },

//  created: function() {
//    this.updateNodes()
//    this.updateLinks()
//  },
  beforeMount: function() {
    Wylib.Common.react(this, {width: 600, height: 600, nodes:{}})
    
    this.updateNodes()
    this.updateLinks()
    Wylib.Wyseman.listen('urnet.async.'+this._uid, 'mychips_admin', dat => {
console.log("Async:", dat)
      if (dat.target == 'peers') this.updateNodes()
      if (dat.target == 'chits' || dat.target == 'tallies') this.updateLinks()
    })
  }
}
</script>
