//Administrator Application main
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
// TODO:
//- 
import Vue from 'vue'
import Wylib from 'wylib'
import AppURNet from './urnet.vue'
Vue.config.productionTip = false

const Template = `
  <wylib-app :tag="tag" :db="dbConf" :title="title" :state="state" :tabs="tabs" :current="state.curTab" @tab="(t)=>{state.curTab = t}" v-slot="ws">
    <component v-for="t in tabs" :key="t.tag" v-show="curTab==t.tag" v-if="hasRun[t.tag]" :is="components[t.tag]" :tag="t.tag" :view="views[t.tag]" :state="state.tabs[t.tag]" :env="ws.env"/>
  </wylib-app>
`
new Vue({
  el: '#app',
  template: Template,
  components: {'wylib-app': Wylib.Application, 'wylib-launch': Wylib.Launcher, 'app-urnet': AppURNet},
  data() { return {
    state:      {curTab: 'users', tabs: {users:{}, conts:{}, urnet:{}, config:{}}},
    tag:	'mychips_admin',
    title:	'MyCHIPs Admin',
    dbConf:	['mychips_admin','wylib'],
    hasRun:	{},
    tabs:	[
      {tag: 'users',  view: 'mychips.users_v', title: 'Users'},
      {tag: 'conts',  view: 'mychips.contracts_v', title: 'Contracts'},
      {tag: 'config', view: 'base.parm_v', title: 'Settings'},
      {tag: 'urnet',  component: 'app-urnet', title: 'Network'},
    ],
  }},
  computed: {
    curTab() {
      return this.state.curTab || 'users'
    },
    views() {
      return this.tabs.reduce((ac,el)=>{
        ac[el.tag] = el.view
        return ac
      }, {})
    },
    components() {
      return this.tabs.reduce((ac,el)=>{
        ac[el.tag] = el.component || 'wylib-launch'
        return ac
      }, {})
    },
  },
//  methods: {
//  },
  mounted: function () {
//console.log("Admin init:", this.curTab)
    if (this.curTab)
      this.$nextTick(()=>{this.$set(this.hasRun, this.curTab, true)})
  },
  watch: {
    'state.curTab': function(newVal, oldVal) {
//console.log("Watched curTab:", newVal)
      this.$set(this.hasRun, this.curTab, true)
    }
  },
})
