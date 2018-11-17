//Admin interface; User Relationship Network Graph
//Copyright MyCHIPs.org: GNU GPL Ver 3; see: License in root of this package
// -----------------------------------------------------------------------------
// TODO:
//X- Find bounding box, including any hubs when resizing canvas
//X- Randomize node placement
//X- Add one more tally to someone
//X- Add optional radius option to nodes, calculate repulsion from edge of radius
//X- Multiple tally hubs stack correctly
//X- Calculate arrows from hub center and end points if hub specified
//X- Can update text in hubs asynchronously
//- Make database generate notifications when users, totals, tallies changed
//- Why don't arrow heads update on hot load?
//- Respond to notifications from database
//- Update nodes when node added
//- Update nodes when removed, disabled
//- Update tallies when added, removed
//- Update tally totals when chits added, removed
//- 

<template>
  <div>
    <div class="header">User Relation Network Graph:</div>
    <button @click="glumph">Update</button>
    <wylib-svgraph :state="state" ref="svg"/>
  </div>
</template>

<script>
import Wylib from 'wylib'
console.log("wylib:", Wylib)

export default {
  components: {'wylib-svgraph': Wylib.SvGraph},
  data() { return {
    state:	{width: 1200, height: 800, nodes: {}},
    tabGap:	40,
    fontSize:	16,
    debits:	9,
    credits:	3,
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
    glumph() {		//For testing only
      let st = this.state.nodes['james_madison.chip']
console.log("ahoy:", st.labels)
      this.$set(st.labels,1,'Howdy!')
      this.$set(st.labels,2,'Ho')
      this.$set(st.labels,3,'There!')
    },
  },
  beforeMount: function() {
    let specu = {view: 'mychips.users_v', fields: ['id', 'std_name', 'peer_cdi'], where: [['id', '>', '1']], order: 1}
    Wylib.Wyseman.request('urnet.user.'+this._uid, 'select', specu, (data,err) => {
      let x = 10, y = 10
      if (data) data.forEach(dat => {
//console.log("U Dat:", dat)
        let { code, ends, width, height } = this.user(dat.id, dat.std_name, dat.peer_cdi)
          , radius = height / 2
        this.$set(this.state.nodes, dat.peer_cdi, {tag:dat.peer_cdi, x, y, width, height, radius, code, ends, links:[], labels:[]})	//So it will react to changes of state
        x += (width + this.tabGap)
        y += (Math.random() * 100 - 50)			//Arranges better by mixing y around a little
        if (x > (this.state.width - width)) {x = 10; y += (height + this.tabGap)}
      })
//console.log("Height:", this.state.height, y + maxHeight)
//      if (this.state.height < (y + maxHeight)) this.state.height = y + maxHeight
    })

    let specl = {view: 'mychips.tallies_v', fields: ['tally_ent', 'tally_seq', 'tally_guid', 'tally_type', 'user_cdi', 'part_cdi'], where: {state: 'open'}, order: [1,2]}
    Wylib.Wyseman.request('urnet.tally.'+this._uid, 'select', specl, (data,err) => {
      let haveHubs = {}						//Keep track of hub stacking
      if (data) data.forEach(dat => {
//console.log("L Dat:", dat)
        if (dat.user_cdi in this.state.nodes) {			//If this node is drawn on the graph
          let node = this.state.nodes[dat.user_cdi]		//Get node's state
            , hubHeight = 20, hubWidth = 100
            , hubYRad = hubHeight/2, hubXRad = hubWidth/2
            , idx = (tag => {
                if (tag in haveHubs) {return (haveHubs[tag] += 1)} else {return (haveHubs[tag] = 0)}
              })(node.tag + dat.tally_type)
            , isFoil = (dat.tally_type == 'foil')
            , xOffset = node.width / 2
            , yOffset = isFoil ? node.height + (hubHeight * (idx + 0.5)) : -hubHeight * (idx + 0.5)
            , color = isFoil ? '#ff8888' : '#8888ff'
            , ends = [{x:xOffset-hubXRad, y:yOffset}, {x:xOffset+hubXRad, y:yOffset}]
            , center = {x:xOffset, y:yOffset}
//console.log("  node:", node, idx, dat.user_cdi, dat.part_cdi)
          this.$set(node.labels, dat.tally_seq, dat.tally_type)
          node.links.push({guid:dat.tally_guid, link:dat.part_cdi, draw:isFoil, ends, center, hub: (lk)=>{
//console.log('Draw hub', node.width, node.height, dat.tally_seq)
            return `
              <g transform="translate(${xOffset}, ${yOffset})">
                <ellipse rx="${hubWidth/2}" ry="${hubHeight/2}" stroke="black" stroke-width="1" fill="${color}"/>
                <text y="5" text-anchor="middle">${node.labels[dat.tally_seq]}</text>
              </g>`
          }})
        }
      })
    })
  }
}
</script>
