//Admin interface; Configuration
//Copyright MyCHIPs.org: GNU GPL Ver 3; see: License in root of this package
// -----------------------------------------------------------------------------
// TODO:
//- 

<template>
  <div>
    <div class="header">Configuration:</div>
    <button @click="initialize()">Initialize</button>
    <div class="subwindows">
      <wylib-win v-for="win,idx in state.windows" v-if="win" topLevel=true :key="idx" :state="win" :tag="'dbp:'+win.client.dbView" :lang="lang(win,idx)" @close="closeWin(idx)">
        <wylib-dbp :state="win.client"/>
      </wylib-win>
    </div>
  </div>
</template>

<script>
import Wylib from 'wylib'

export default {
  name: 'app-config',
  components: {'wylib-win': Wylib.Window, 'wylib-dbp': Wylib.DataView},
  props: {
    state:	{type: Object, default: ()=>({})},
  },
  inject: ['top'],			//Where to send modal messages
  data() { return {
    winRec:	{posted: true, x: 40, y: 220, client: {dbView: 'base.parm_v'}},
//    state:	{windows: [{posted: true, y: 220, client: {dbView: 'base.parm_v', loaded: true}}]},
  }},

  methods: {
    lang: function(win,idx) { return {
      title:	win.client.dbView + ':' + idx, 
      help:	'Preview listing of view: ' + win.client.dbView
    }},
    addWin() {
//console.log("Add Window")
      let wins = this.state.windows
        , newState = Wylib.Common.clone(this.winRec)
      newState.x += (Math.random() - 0.5) * 100
      newState.y += (Math.random() - 0.5) * 100
      for(var i = 0; wins[i]; i++); wins.splice(i, 1, newState)
    },
    closeWin(idx) {
console.log("Close Window", idx)
      this.state.windows[idx] = null
      this.$forceUpdate()
    },
    initialize() {
      console.log("Initializing...")
    }
  },

  beforeMount: function() {
    Wylib.Common.react(this, {windows: [this.winRec]})
  },
}
</script>
