//Admin interface; Users data
//Copyright MyCHIPs.org: GNU GPL Ver 3; see: License in root of this package
// -----------------------------------------------------------------------------
// TODO:
//- Get rid of reference to siteSocket
//- 

<template>
  <div>
    <div class="header">User Accounts:</div>
    <div class="subwindows">
      <wylib-win v-for="win,idx in state.windows" v-if="win" topLevel=true :key="idx" :state="win" :lang="lang(win,idx)" @close="closeWin(idx)">
        <wylib-dbp slot-scope="ws" :top="ws.top" :state="win.client"/>
      </wylib-win>
    </div>
    <div class="instructions">
      <p>Use this screen for importing and managing users.</p>
      <p>Press this button:
           <button @click="addWin">New User Preview</button>
         to create as many more windows as you like.</p>
      <p>Or, use this button:
           <button @click="ticket">Ticket Preview</button>
         to generate a ticket for the current user.</p>
      <p>You can import a new user from a JSON file by dragging the file into the Importer box below.</p>
    </div>
    <br>
    <div class="importer">
      File Importer:
      <input type="file" @change="importFile" accept="*.json" multiple title="Select or drag files here to import JSON data directly."/>
    </div>
  </div>
</template>

<script>
import Wylib from 'wylib'

export default {
  components: {'wylib-win': Wylib.Window, 'wylib-dbp': Wylib.DataView},

  data() { return {
    dbView:	'mychips.users_v',
    winRec:	{posted: true, x: 40, y: 70, client: {dbView: 'mychips.users_v'}},
//    state:	{windows: []},
    state:	{windows: [{posted: true, y: 220, client: {dbView: 'mychips.users_v', loaded: true}}]},
  }},

  methods: {
    lang: function(win,idx) { return {
      title:	win.client.dbView + ':' + idx, 
      help:	'Preview listing of view: ' + win.client.dbView
    }},
    ticket() {
console.log("Preview Ticket")
    },
    addWin() {
//console.log("Add Window")
      let wins = this.state.windows
      for(var i = 0; wins[i]; i++); wins.splice(i,1,Wylib.Common.clone(this.winRec))
    },
    closeWin(idx) {
console.log("Close Window", idx)
      this.state.windows[idx] = null
      this.$forceUpdate()
    },
    importFile(ev) {
      let i, f; for (let i = 0, f; f = ev.target.files[i]; i++) {
        let reader = new FileReader();
        reader.addEventListener('load', function() {
          let jdat = JSON.stringify(reader.result)
          console.log("Result:" + jdat)
          siteSocket.send('import', jdat)
        })
        reader.readAsText(f)
      }
    },
  },
}
</script>
