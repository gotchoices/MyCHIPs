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
      <wylib-win v-for="win,idx in state.windows" v-if="win" topLevel=true :key="idx" :state="win" :tag="'dbp:'+win.client.dbView" :lang="lang(win,idx)" @close="closeWin(idx)">
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
//    dbView:	'mychips.users_v',
    winRec:	{posted: true, x: 50, y: 220, client: {dbView: 'mychips.users_v'}},
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
        , newState = Wylib.Common.clone(this.winRec)
      newState.x += (Math.random() - 0.5) * 100
      newState.y += (Math.random() - 0.5) * 100
      for(var i = 0; wins[i]; i++); wins.splice(i, 1, newState)
    },
    closeWin(idx) {
//console.log("Close Window", idx)
      this.state.windows[idx] = null
      this.$forceUpdate()
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
    Wylib.Common.react(this, {windows: []})
    this.addWin()
  },
}
</script>
