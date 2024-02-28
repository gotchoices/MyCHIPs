//User Application main
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
// TODO:
//- 
import { createApp } from 'vue'
import App from './user.vue'
import Wylib from 'wylib'

const app = createApp(App)
app.component('wylib-app', Wylib.Application)
app.mount('#app')
