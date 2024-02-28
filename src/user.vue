//User Application main
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
// TODO:
//- 
<template>
  <wylib-app :tag="tag" :db="dbConf" :title="title" :state="state" :tabs="tabs" :current="state.curTab" @tab="(t)=>{state.curTab = t}" v-slot="ws">
    <component v-for="t in runTabs" :key="t.tag" v-show="curTab==t.tag" :is="components[t.tag]" :tag="t.tag" :view="views[t.tag]" :state="state.tabs[t.tag]" :env="ws.env"/>
  </wylib-app>
</template>

<script>
import Wylib from 'wylib'

export default {
  components: {'wylib-app': Wylib.Application, 'wylib-launch': Wylib.Launcher},
  data() { return {
    state:      {curTab: 'dash', tabs: {dash:{}, user:{}, tallies:{}}},
    tag:	'mychips_user',
    title:	'MyCHIPs User Portal',
    dbConf:	['mychips_user','wylib'],
    hasRun:	{},
    tabs:	[
//      {tag: 'dash', component: 'app-visbs', title: 'Dashboard'},
      {tag: 'user', view: 'mychips.users_v_me', title: 'Profile'},
      {tag: 'tallies', view: 'mychips.tallies_v_me', title: 'Tallies'},
//      {tag: 'config', view: 'base.parm_v', title: 'Settings'},
    ],
    currentTab: 'dash'
  }},
  computed: {
    curTab() {
      return this.state.curTab || 'users'
    },
    runTabs() {		//Defer loading component until a tab has been selected
      return this.tabs.filter(t => this.hasRun[t.tag])
    },
    views() {
      return this.tabs.reduce((ac,el)=>{
        let aggObj = {[el.tag]: el.view}
        Object.assign(aggObj, ac)
        return aggObj
      }, {})
    },
    components() {
      return this.tabs.reduce((ac,el)=>{
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
