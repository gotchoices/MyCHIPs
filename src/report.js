//Report window manager
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
// TODO:
//- 
import Vue from 'vue'
import Wylib from 'wylib'
Vue.config.productionTip = false
Vue.config.devtools = false

new Vue({
  el: '#app',
  template: '<wylib-pop></wylib-pop>',
  components: { 'wylib-pop': Wylib.Popup},
})
