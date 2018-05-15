//User Application main
//Copyright MyCHIPs.org: GNU GPL Ver 3; see: License in root of this package
// -----------------------------------------------------------------------------
// TODO:
//- 
import Vue from 'vue'
Vue.config.productionTip = false

import User from './User.vue'

new Vue({
  el: '#app',
  template: '<User/>',
  components: { User }
})
