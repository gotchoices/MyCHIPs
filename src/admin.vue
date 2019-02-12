//Administrator client, main component
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
// TODO:
//- Pull application text from database
//- 
<template>
  <wylib-app tag="mychips_admin" title="MyCHIPs Administration" :db="dbConf" :state="state" :tabs="tabs" :current="state.curTab" @tab="(t)=>{state.curTab = t}">
    <keep-alive><component :is="'app-' + state.curTab" :state="state.tabs[state.curTab]"/></keep-alive>
  </wylib-app>
</template>

<script>
import Wylib from 'wylib'
import AppConts from './admin/conts.vue'
import AppUsers from './admin/users.vue'
import AppURNet from './admin/urnet.vue'
import AppConfig from './admin/config.vue'

export default {
  components: {'wylib-app': Wylib.Application, 'app-users': AppUsers, 'app-conts': AppConts, 'app-urnet': AppURNet, 'app-config': AppConfig},
  data() { return {
    state:      {curTab: 'users', tabs: {users:{}, conts:{}, urnet:{}, config:{}}},
    tog:	true,
    tabs:	[
      {tag: 'users', title: 'Users'},
      {tag: 'conts',  title: 'Contracts'},
      {tag: 'urnet',  title: 'Network'},
      {tag: 'config', title: 'Settings'},
    ],
    dbConf: "['mychips_admin','wylib']"
  }},
//  methods: {
//  },
//  mounted: function () {
//  },
}
</script>

<style>
</style>
