//User client, main component
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
// TODO:
//- 
<template>
  <wylib-app tag="mychips_user" title="MyCHIPs User Access" :tabs="tabs" :current="currentTab" @tab="(t)=>{currentTab = t}">
    <keep-alive><component :is="'app-' + currentTab"/></keep-alive>
  </wylib-app>
</template>

<script>
import Wylib from 'wylib'
import AppDash from './user/dash.vue'
import AppPeers from './user/peers.vue'
import AppTallies from './user/tallies.vue'
import AppConfig from './user/config.vue'

export default {
  components: {'wylib-app': Wylib.Application, 'app-dash': AppDash, 'app-peers': AppPeers, 'app-tallies': AppTallies},
  data() { return {
    state:      {},
    tog:	true,
    tabs:	[
      {tag: 'dash', title: 'Dashboard'},
      {tag: 'peers',  title: 'Peers'},
      {tag: 'tallies', title: 'Tallies'},
      {tag: 'config', title: 'Configuration'},
    ],
    currentTab: 'dash'
  }},
//  methods: {
//  },
//  mounted: function () {
//  },
}
</script>

<style lang='less'>
</style>
