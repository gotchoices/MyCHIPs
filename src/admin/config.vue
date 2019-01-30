//Admin interface; Configuration
//Copyright MyCHIPs.org: GNU GPL Ver 3; see: License in root of this package
// -----------------------------------------------------------------------------
// TODO:
//- 

<template>
  <div>
    <div class="header">Configuration Settings:</div>
    <div class="subwindows">
      <wylib-win v-for="win,key in state.windows" topLevel=true :key="key" :state="win" @close="r=>{closeWin(key,r)}">
        <wylib-dbp :state="win.client"/>
      </wylib-win>
    </div>
    <button @click="addWin()">New Configuration Preview</button>
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
    addWin() {Wylib.Common.addWindow(this.state.windows, this.winRec, this, true)},
    closeWin(idx, reopen) {Wylib.Common.closeWindow(this.state.windows, idx, this, reopen)},
  },

  beforeMount: function() {
    Wylib.Common.stateCheck(this)
    if (Object.keys(this.state.windows).length <= 0) this.addWin()
  },
}
</script>
