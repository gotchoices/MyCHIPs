//Graphical view of a user's net worth in CHIPs
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
// TODO:
//- Make example graphical visualizer
//- Use SVGraph.vue?  Or something else?
//- 

<template>
  <div class="visbs">
    <div class="header">User Visual Balance Sheet:</div>
    <wylib-svgraph :state="state" ref="svg" @refresh="refresh" @reset="reset"/>
  </div>
</template>

<script>
const Wylib = require('wylib')

export default {
  name: 'app-visbs',
  components: {'wylib-svgraph': Wylib.SvGraph},
  props: {
    state:	{type: Object, default: ()=>({})},
  },
  inject: ['top'],			//Where to send modal messages
  data() { return {
    xyz:	null,
  }},
  computed: {
    abc: function() {
      return true
    },
  },
  methods: {
    qrs() {
      return true
    },
    refresh() {
    },
    reset() {
    },
  },

//  created: function() {
//  },
  beforeMount: function() {
  },
    
  mounted: function() {
  }
}
</script>

<style lang='less'>
</style>
