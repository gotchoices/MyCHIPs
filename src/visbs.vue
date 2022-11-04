//Graphical view of a user's net worth in CHIPs
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
// TODO:
//- Obsolete file?
//- Make example graphical visualizer
//- Use SVGraph.vue?  Or something else?
//- 

<template>
  <div class="visbs">
    <div class="header">User Visual Balance Sheet:</div>
    <wylib-svgraph :state="state" ref="svg" @refresh="refresh" @reset="reset"/>
  </div>
</template>

<script>
import Wylib from 'wylib'

export default {
  name: 'app-visbs',
  components: {'wylib-svgraph': Wylib.SvGraph},
  props: {
    state:	{type: Object, default: ()=>({})},
  },
  inject: ['top'],			//Where to send modal messages
  data() { return {
    xyz:	null,
  }},
  computed: {
    abc: function() {
      return true
    },
  },
  methods: {
    peer(dat) {				//Generate SVG code for a user/peer node
//console.log("User", dat.id, dat.peer_cid, this.totals[dat.peer_cid])
      let { id, std_name, peer_cid, peer_sock, user_ent } = dat
        , fColor = (dat.total < 0 ? '#ff0000' : '#0000ff')
        , sumLine = user_ent ? `${dat.stock_tot.toFixed(3)} - ${-dat.foil_tot.toFixed(3)} = <tspan stroke="${fColor}" fill="${fColor}">${dat.total.toFixed(3)}</tspan>` : ''
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

    updateValues() {
      let where = {state: 'open'}
        , fields = ['tally_ent', 'tally_seq', 'tally_type', 'partner', 'total']
        , spec = {view: 'mychips.tallies_v_me', fields, where, order: 2}

console.log('UpdateValues:', spec)
      Wylib.Wyseman.request('visbs.values.'+this._uid, 'select', spec, (data,err) => {

//        let notFound = Object.assign({}, this.state.nodes)	//Track any nodes on our graph but no longer returned in the query
//          , needLinks = {}
console.log("Update values:", this.state.nodes, data.length, data)
return
        for (let t of data) {					//For each tally
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
    },

    updateNodes(dTime) {
console.log('UpdateNodes')
return
    },		//updateNodes

    refresh() {			//Readjust to any new nodes
      this.updateNodes()
    },
    reset() {			//Start over with random placement
      this.state.nodes = {}
      this.updateValues()
      this.updateNodes()
    },
  },

//  created: function() {
//  },
  beforeMount: function() {
    Wylib.Common.stateCheck(this)
    
    Wylib.Wyseman.listen('visbs.async.'+this._uid, 'mychips_user', dat => {
console.log("VisBS async:", dat)

//      if (dat.target == 'peers' || dat.target == 'tallies')
//        this.updateNodes(dat.oper == 'DELETE' ? null : dat.time)
//      this.$refs.svg.$emit('change')
    })
  },
    
  mounted: function() {
    this.updateValues()
    this.updateNodes()
  }
}
</script>

<style lang='less'>
</style>
