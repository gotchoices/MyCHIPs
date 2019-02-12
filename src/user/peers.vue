//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
<template>
 <div>
  <wylib-win v-for="win,idx in state.windows" v-if="win" topLevel=true :key="idx" :state="win" :lang="lang(win,idx)" @close="closeWin(idx)">
    <wylib-dbp slot-scope="ws" :top="ws.top" :state="win.client"/>
  </wylib-win>
 </div>
</template>

<script>
import Wylib from 'wylib'

export default {
  components: {'wylib-win': Wylib.Window, 'wylib-dbp': Wylib.DataView},

  data() { return {
    dbView:	'mychips.users_v',
//    state:	{windows: []},
    state:	{windows: [{posted: true, client: {dbView: 'mychips.users_v', loaded: true}}]},
  }},

  methods: {
    lang: function(win,idx) { return {
      title:	win.client.dbView + ':' + idx, 
      help:	'Preview listing of view: ' + win.client.dbView
    }},
    addWin() {
console.log("Add Window")
      this.state.windows.push(this.winRec)
    },
    closeWin(idx) {
console.log("Close Window", idx)
      this.state.windows[idx] = null
      this.$forceUpdate()
    },
  },
}
</script>
