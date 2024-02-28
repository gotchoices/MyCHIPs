//Report window manager
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
// TODO:
//- 
import { createApp } from 'vue'
import App from './report.vue'
import Wylib from 'wylib'

const app = createApp(App)
app.component('wylib-pop', Wylib.Popup)
app.mount('#app')
