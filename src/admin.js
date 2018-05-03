//Administrator Application main
//Copyright MyCHIPs.org: GNU GPL Ver 3; see: License in root of this package
// -----------------------------------------------------------------------------
// TODO:
//- Change connect code to use wylib
//- 
import Vue from 'vue'
Vue.config.productionTip = false

import Admin from './Admin.vue'

new Vue({
  el: '#app',
  template: '<Admin/>',
  components: { Admin }
})
