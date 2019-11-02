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
    peer(dat) {				//Generate SVG code for a user/peer node
//console.log("User", dat.id, dat.peer_cdi, this.totals[dat.peer_cdi])
      let { id, std_name, peer_cdi, peer_sock, user_ent } = dat
        , fColor = (dat.total < 0 ? '#ff0000' : '#0000ff')
        , sumLine = user_ent ? `${dat.stock_tot} - ${-dat.foil_tot} = <tspan stroke="${fColor}" fill="${fColor}">${dat.total}</tspan>` : ''
        , yOff = this.fontSize + 3
        , host = peer_sock.split('.')[0]
        , cdiLine = `${peer_cdi}@${host}`
        , text = `
        <text x="4" y="${yOff}" style="font:normal ${this.fontSize}px sans-serif;">
          ${id}:${std_name}
          <tspan x="4" y="${yOff * 2}">${cdiLine}</tspan>
          <tspan x="4" y="${yOff * 3}">${sumLine}</tspan>
        </text>`
        , max = Math.max(cdiLine.length + 2, std_name.length + 6, sumLine.length-48)	//take tspan into account
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

    updateLink(i, idx, cdi, dat) {
      let node = this.state.nodes[cdi]					//Get node's state object
        , guid = dat.guids[i]
        , isFoil = (dat.types[i] == 'foil')
        , amount = dat.totals[i]
        , link = dat.part_cdis[i]
        , inside = dat.insides[i]
        , noDraw = (isFoil && inside)
        , reverse = (isFoil && !inside)
        , nodeLink = node.links.find(lk => (lk.index == guid))	//Do we already have a definition for this link?
        , xOffset = node.width / 2
        , yOffset = isFoil ? node.height + (this.hubHeight * (idx + 0.5)) : -this.hubHeight * (idx + 0.5)	//Stack it on top (stocks) or on bottom (foils)
        , hubColor = amount == 0 ? '#f0f0f0' : (amount < 0 ? '#F0B0B0' : '#B0B0F0')
        , color = dat.states[i] == 'open' ? 'blue' : 'orange'
        , hubYRad = this.hubHeight/2, hubXRad = this.hubWidth/2
        , ends = [{x:xOffset-hubXRad, y:yOffset}, {x:xOffset+hubXRad, y:yOffset}]
        , center = {x:xOffset, y:yOffset}

      if (!nodeLink) {				//Create new data structure for link, hubs
        nodeLink = {index:guid, link, ends, color, center, noDraw:null, reverse:null, found:true, hub:null}
        node.links.push(nodeLink)
      }
//console.log("  link:", link, node, idx, cdi, amount, yOffset, nodeLink)
      Object.assign(nodeLink, {ends, center, color, link, noDraw, reverse, found:true, hub: ()=>{
        return `<g transform="translate(${center.x}, ${center.y})">
          <ellipse rx="${hubXRad}" ry="${hubYRad}" stroke="black" stroke-width="1" fill="${hubColor}"/>
          <text y="${hubYRad/2}" text-anchor="middle" style="font:normal ${this.fontSize}px sans-serif;">${amount}</text>
        </g>`
      }})
    },

    updateNodes(dTime) {
      let where = [['peer_ent', 'notnull']]
        , fields = ['id', 'std_name', 'peer_cdi', 'peer_sock', 'user_ent', 'total', 'stock_tot', 'foil_tot', 'tallies', 'types', 'totals', 'states', 'guids', 'part_cdis', 'insides']
        , spec = {view: 'mychips.users_v_tallysum', fields, where, order: 1}
      if (dTime) where.push(['latest', '>=', dTime])

      Wylib.Wyseman.request('urnet.peer.'+this._uid, 'select', spec, (data,err) => {
        let notFound = Object.assign({}, this.state.nodes)
//console.log("Update nodes:", dTime, this.state.nodes, data.length, data)
        for (let d of data) {
          let bodyObj = this.peer(d)
            , radius = bodyObj.height / 2
            , cdi = d.peer_cdi
          if (cdi in this.state.nodes) {
            Object.assign(this.state.nodes[cdi], bodyObj, {radius})
//console.log("n Dat:", cdi, this.state.nodes[cdi].body)
          } else {
            let x = Math.random() * this.state.width/2
              , y = Math.random() * this.state.height/2
            this.$set(this.state.nodes, cdi, Object.assign(bodyObj, {tag:cdi, x, y, radius, links:[]}))
//console.log("N Dat:", cdi, x, y)
          }
//console.log("Dat:", d)
          let stocks = 0, foils = 0
          for (let i = 0; i < d.tallies; i++) {
            let idx = (d.types[i] == 'stock') ? stocks++ : foils++
            this.updateLink(i, idx, cdi, d)
          }
          let node = this.state.nodes[cdi]
          for (let i = node.links.length - 1; i >= 0; i--) {
            let link = node.links[i]
//console.log("  checking:", i, link, link.found)
            if (!dTime && !link.found) node.links.splice(i,1)		//Delete if not found this iteration
            link.found = false
          }
          
          delete notFound[cdi]					//Note we processed this node
        }
//console.log("Not found:", notFound, this.state.nodes)
        if (!dTime) Object.keys(notFound).forEach(key=>{	//Delete anything on the SVG, not now in nodes
          this.$delete(this.state.nodes, key)
        })
      })
    },		//updateNodes

    refresh() {
      this.updateNodes()
    },
    reset() {
      this.state.nodes = {}
      this.updateNodes()
    },
  },

  beforeMount: function() {
    Wylib.Common.stateCheck(this)
    
    Wylib.Wyseman.listen('urnet.async.'+this._uid, 'mychips_admin', dat => {
//console.log("URnet async:", dat)

      if (dat.target == 'peers')
        this.updateNodes(dat.oper == 'DELETE' ? null : dat.time)
      if (dat.target == 'tallies')
        this.updateNodes(dat.oper == 'DELETE' ? null : dat.time)
    })
  },

  mounted: function() {
    this.updateNodes()
  }
}
</script>
