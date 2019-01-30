//Report window manager
//Copyright MyCHIPs.org: GNU GPL Ver 3; see: License in root of this package
// -----------------------------------------------------------------------------
// TODO:
//- 
import Vue from 'vue'
import Wylib from 'wylib'
Vue.config.productionTip = false

const Template = `
  <wylib-pop :state="state" @submit="submit">
    <div v-if="state.format == 'html'" v-html="state.content"/>
    <component v-else :is="compName" :state="state.content"/>
  </wylib-pop>
`

new Vue({
  el: '#app',
  data() { return {
    state:      {format: 'dialog', content: {}},
  }},
  template: Template,
  components: { 'wylib-pop': Wylib.Popup, 'wylib-dialog': Wylib.Dialog, 'wylib-strdoc': Wylib.StructDoc},
  computed: {
    compName: function() {
      if (!this.state.format || this.state.format == 'html') return null
      if (this.state.format.includes('-')) return this.state.format
      return 'wylib-' + this.state.format
    },
  },

  methods: {
    kahuna: function() {
      return window.opener || window.parent
    },
    submit: function(...args) {
console.log("Got submit from content:", ...args)
      this.kahuna().postMessage({request:'submit'}, '*')
    },
  },

  mounted: function() {
//console.log("Popup mounted:", this.kahuna())
    this.kahuna().postMessage({request:'ready'}, location.origin)	//Let parent window know we are ready to load content

    window.addEventListener('message', (ev) => {	//Answer replies from the parent window
//console.log("Popup got message:", ev.source, ev.data)
      let { request, format, content, config } = ev.data
        , { action } = config || {}
      if (request != 'populate' || !format) return
//console.log("Popup got request:", request, format, content, config)
      this.state.format = format
      this.state.content = content
      if (window.opener && action) window.document.title = action.lang.title
    })
  },
})
