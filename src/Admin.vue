//Administrator client, main component
//Copyright MyCHIPs.org: GNU GPL Ver 3; see: License in root of this package
// -----------------------------------------------------------------------------
// TODO:
//- Pull application text from database
//- 
<template>
  <wylib-app tag="mychips_admin" title="MyCHIPs Administration" :state="state" :tabs="tabs" :current="state.curTab" @tab="(t)=>{state.curTab = t}">
    <keep-alive><component :is="'app-' + state.curTab" :state="state.tabs[state.curTab]"/></keep-alive>
  </wylib-app>
</template>

<script>
import Wylib from 'wylib'
import AppDocs from './admin/docs.vue'
import AppUsers from './admin/users.vue'
import AppURNet from './admin/urnet.vue'
import AppConfig from './admin/config.vue'

export default {
  components: {'wylib-app': Wylib.Application, 'app-users': AppUsers, 'app-docs': AppDocs, 'app-urnet': AppURNet, 'app-config': AppConfig},
  data() { return {
    state:      {curTab: 'users', tabs: {users:{}, docs:{}, urnet:{}, config:{}}},
    tog:	true,
    tabs:	[
      {tag: 'users', title: 'Users'},
      {tag: 'docs',  title: 'Documents'},
      {tag: 'urnet',  title: 'Network'},
      {tag: 'config', title: 'Settings'},
    ],
  }},
  methods: {
  },
  mounted: function () {
  },
}
</script>

<style>
</style>
