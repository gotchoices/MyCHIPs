//Admin interface; Contract Documents
//Copyright MyCHIPs.org: GNU GPL Ver 3; see: License in root of this package
// -----------------------------------------------------------------------------
// TODO:
//- Allow to easily load document preview/editor from dbe action
//- Allow to run in wylib-win or separate browser window
//- How to save, save-as?
//- Can create new documents
//- Can publish with action, writes date, makes document read-only
//- Can query database for document version, fetch/compare hash
//- DB will fetch missing documents from the cited URL
//- Install standard contracts we have so far into the editor and DB
//- Publish our standard contracts on mychips.org (defined locally)
//- How to include other documents
//- Can render by reference only, or by full in-line inclusion
//- 
//- Can I export a tally to paper as a contract with ledger appendix?
//- Can the ledger go into a series of QR codes?
//- 
//- Later:
//- Any way to print with QR codes
//- 

<template>
  <div>
    <div class="header">Contract Documents:</div>
    <div class="subwindows">
      <wylib-win v-for="win,key in state.windows" topLevel=true :key="key" :state="win" @close="r=>{closeWin(key,r)}">
        <wylib-dbp :state="win.client"/>
      </wylib-win>

<!-- For testing:
      <wylib-win topLevel=true :state="state.doc">
        <wylib-strdoc :state="state.doc.client"/>
      </wylib-win>
 -->
    </div>
    <button @click="addWin()">New Contract Preview</button>
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
  name: 'app-conts',
//  components: {'wylib-win': Wylib.Window, 'wylib-dbp': Wylib.DataView},
  components: {'wylib-win': Wylib.Window, 'wylib-dbp': Wylib.DataView, 'wylib-strdoc': Wylib.StructDoc},
  props: {
    state:	{type: Object, default: ()=>({})},
  },
  inject: ['top'],			//Where to send modal messages
  data() { return {
    winRec:	{posted: true, x: 40, y: 220, client: {dbView: 'mychips.contracts_v'}},

//    stateTpt:	{windows: {}},
//For testing:
stateTpt:	{windows: {}, doc: {posted:true, x:10, y:20, client: {
  title: "My Section",
  text: "This is a test of the all new system of typing",
  subs: []
}}},
  }},

  methods: {
    addWin() {Wylib.Common.addWindow(this.state.windows, this.winRec, this, true)},
    closeWin(idx, reopen) {Wylib.Common.closeWindow(this.state.windows, idx, this, reopen)},
    importFile: Import,
  },

  beforeMount: function() {
    Wylib.Common.stateCheck(this)
    if (Object.keys(this.state.windows).length <= 0) this.addWin()
  },
}
</script>
