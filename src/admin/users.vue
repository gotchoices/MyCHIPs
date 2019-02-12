//Admin interface; Users data
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
// TODO:
//- Report errors on file import
//- 

<template>
  <div>
    <div class="header">User Accounts:</div>
    <div class="subwindows">
      <wylib-win v-for="win,key in state.windows" topLevel=true :key="key" :state="win" @close="r=>{closeWin(key,r)}">
        <wylib-dbp :state="win.client"/>
      </wylib-win>
    </div>
    <div class="instructions">
      <p>Use this screen for importing and managing users.</p>
      <p>Press this button:
           <button @click="addWin">New User Preview</button>
         to create as many more windows as you like.</p>
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
import Import from './import.js'

export default {
  name: 'app-users',
  components: {'wylib-win': Wylib.Window, 'wylib-dbp': Wylib.DataView},
  props: {
    state:	{type: Object, default: ()=>({})},
  },
  inject: ['top'],			//Where to send modal messages
  data() { return {
    stateTpt:	{windows: {}},
  }},

  methods: {
    addWin() {
      let newState = {posted: true, client: {dbView: 'mychips.users_v'}}
      Wylib.Common.addWindow(this.state.windows, newState, this, true)
    },
    closeWin(idx, reopen) {Wylib.Common.closeWindow(this.state.windows, idx, this, reopen)},
    importFile: Import,
  },
  
  beforeMount: function() {
    Wylib.Common.stateCheck(this)
    if (Object.keys(this.state.windows).length <= 0) this.addWin()
  },
}
</script>
