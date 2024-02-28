//Administrator Application main component
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
// TODO:
//- 

<template>
  <wylib-app :tag="tag" :db="dbConf" :title="title" :state="state" :tabs="tabs" :current="state.curTab" @tab="(t)=>{state.curTab = t}">
    <template v-slot:default="ws">
      <component v-for="t in runTabs" :key="t.tag" v-show="curTab==t.tag" :is="components[t.tag]" :tag="t.tag" :view="views[t.tag]" :state="state.tabs[t.tag]" :env="ws.env"/>
    </template>
  </wylib-app>
</template>

<script>
import Wylib from 'wylib'
import URNet from './urnet.vue'
import TabEdit from 'wyclif/src/wysegi/tabedit.vue'

export default {
  components: {'wylib-launch': Wylib.Launcher, 'app-urnet': URNet, 'wc-tabedit': TabEdit},
  data() { return {
    state: {
      curTab: 'users',
      tabs: {
        users:{}, agents: {}, conts:{}, urnet:{}, creds:{}, config:{},
        db: {windows: [{posted: true, client: {dbView: 'wm.table_pub', loaded: true}}]}
      }
    },
    tag:	'mychips_admin',
    title:	'MyCHIPs Admin',
    dbConf:	['mychips_admin','wylib'],
    hasRun:	{},
    tabs:	[
      {tag: 'users',  view: 'mychips.users_v', title: 'Users'},
      {tag: 'agents', view: 'mychips.agents_v', title: 'Agents'},
      {tag: 'conts',  view: 'mychips.contracts_v', title: 'Contracts'},
      {tag: 'creds',  view: 'mychips.creds_v', title: 'Cert Scoring'},
      {tag: 'config', view: 'base.parm_v', title: 'Settings'},
      {tag: 'urnet',  component: 'app-urnet', title: 'Network'},
      {tag: 'db', component: 'wc-tabedit', title: 'Database'},
    ],
  }},
  computed: {
    curTab() {		//Currently selected tab
      return this.state.curTab ?? 'users'
    },
    runTabs() {		//Defer loading component until a tab has been selected
      return this.tabs.filter(t => this.hasRun[t.tag])
    },
    views() {
      return this.tabs.reduce((ac, el) => {
        let aggObj = {[el.tag]: el.view}
        Object.assign(aggObj, ac)
        return aggObj
      }, {})
    },
    components() {
      return this.tabs.reduce((ac, el)=>{
        let aggObj = {[el.tag]: el.component ?? 'wylib-launch'}
        Object.assign(aggObj, ac)
        return aggObj
      }, {})
    },
  },
//  methods: {
//  },
  mounted: function () {
//console.log("Admin init:", this.curTab)
    if (this.curTab)
      this.$nextTick(()=>{this.hasRun[this.curTab] = true})
  },
  watch: {
    'state.curTab': function(newVal, oldVal) {
//console.log("Watched curTab:", newVal)
      this.hasRun[this.curTab] = true
    }
  },
}
</script>
