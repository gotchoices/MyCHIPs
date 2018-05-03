//User Application main
//Copyright MyCHIPs.org: GNU GPL Ver 3; see: License in root of this package
// -----------------------------------------------------------------------------
// TODO:
//- 
import Vue from 'vue'
import VueRouter from 'vue-router'
Vue.use(VueRouter)

//Vue.config.productionTip = false
import User from './User.vue'
import HomeComp from './user/HomeComp.vue'
import PeersComp from './user/PeersComp.vue'
import ConfigComp from './user/ConfigComp.vue'

const routes = [
  {path: '/',		component: HomeComp	},
  {path: '/peers',	component: PeersComp	},
  {path: '/config',	component: ConfigComp	}
]

const router = new VueRouter({routes})
new Vue({
  el: '#app',
  router,
  template: '<User/>',
  components: { User }
})
