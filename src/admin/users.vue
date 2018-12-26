//Admin interface; Users data
//Copyright MyCHIPs.org: GNU GPL Ver 3; see: License in root of this package
// -----------------------------------------------------------------------------
// TODO:
//- Report errors on file import
//- 

<template>
  <div>
    <div class="header">User Accounts:</div>
    <div class="subwindows">
      <wylib-win v-for="win,idx in state.windows" v-if="win" topLevel=true :key="idx" :state="win" @close="r=>{closeWin(idx,r)}">
        <wylib-dbp :state="win.client"/>
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
  name: 'app-users',
  components: {'wylib-win': Wylib.Window, 'wylib-dbp': Wylib.DataView},
  props: {
    state:	{type: Object, default: ()=>({})},
  },
  inject: ['top'],			//Where to send modal messages
  data() { return {
    winRec:	{posted: true, x: 50, y: 220, client: {dbView: 'mychips.users_v'}},
    stateTpt:	{windows: []},
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
      Wylib.Common.addWindow(this.state.windows, this.winRec, true)
    },
    closeWin(idx, reopen) {
      wylib.Common.closeWindow(this.state.windows, idx, reopen)
    },

    importFile(ev) {
      let i, f; for (let i = 0, f; f = ev.target.files[i]; i++) {
        let reader = new FileReader();
        reader.onload = ()=>{
          let jdat = reader.result	//JSON.stringify(reader.result)
//console.log("Jdat:" + jdat)
          let spec = {view: 'json.import(jsonb)', params: [jdat]}
          Wylib.Wyseman.request('users.import.'+this._uid, 'tuple', spec, (res, err) => {
            if (err) this.top.error(err)
//console.log("Import res:", res)
          })
        }
        reader.readAsText(f)
      }
    },
  },
  
  beforeMount: function() {
    Wylib.Common.stateCheck(this)
    if (this.state.windows.length <= 0) this.addWin()
  },
}
</script>
