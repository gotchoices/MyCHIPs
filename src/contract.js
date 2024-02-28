//Contract document viewer
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------

import { createApp } from 'vue'
import App from './contract.vue'
const Wylib = require('wylib')

const app = createApp(App)
app.component('wylib-strdoc', Wylib.StructDoc)
app.mount('#app')
