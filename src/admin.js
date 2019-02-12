//Administrator Application main
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
// TODO:
//- Change connect code to use wylib
//- 
import Vue from 'vue'
Vue.config.productionTip = false

import Admin from './admin.vue'

new Vue({
  el: '#app',
  template: '<Admin/>',
  components: { Admin }
})
