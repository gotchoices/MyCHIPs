//User Application main
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
// TODO:
//- 
import Vue from 'vue'
Vue.config.productionTip = false

import User from './user.vue'

new Vue({
  el: '#app',
  template: '<User/>',
  components: { User }
})
