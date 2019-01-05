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
      <wylib-win v-for="win,idx in state.windows" v-if="win" topLevel=true :key="idx" :state="win" @close="r=>{closeWin(idx,r)}">
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
    stateTpt:	{windows: []},
  }},

  methods: {
    lang: function(win,idx) { return {
      title:	win.client.dbView + ':' + idx, 
      help:	'Preview listing of view: ' + win.client.dbView
    }},
    addWin() {
      Wylib.Common.addWindow(this.state.windows, this.winRec, true)
    },
    closeWin(idx, reopen) {
      Wylib.Common.closeWindow(this.state.windows, idx, reopen)
    },
    initialize() {
      console.log("Initializing...")
    }
  },

  beforeMount: function() {
    Wylib.Common.stateCheck(this)
    if (this.state.windows.length <= 0) this.addWin()
  },
}
</script>
