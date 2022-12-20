//Contract document viewer
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
// TODO:
//- Can check validity of hash in browser?
//- 
import Vue from 'vue'
Vue.config.productionTip = false
Vue.config.devtools = false

const Wylib = require('wylib')
const Stringify = require('json-stable-stringify')
const Hash = require('hash.js')

const TopHandler = function(context) {			//Mimick top in wylib
  this.context = context
console.log("context:", context)
}
var template = `
    <div>
      <h3>{{ key }} {{ optDigest }}</h3>
      <wylib-strdoc :editable="false" :env="env" :state="state"/>
    </div>`

new Vue({
  el: '#app',
  data() { return {
    top:	null,
    env:	{pr:{}, wm:{h:{},t:{}}},			//Dummy structure for help/language
    state:	{tag:null, name:null, text:null, title:null, sections:[]},
    key:	null,
    digest:	null,			//Digest that comes with the document
    digested:	null,			//Digest we calculate locally
  }},
  provide() { return {
    app: () => {return this.top},
    top: () => {return this.top},
  }},
  template,
  components: { 'wylib-strdoc': Wylib.StructDoc},
  computed: {
    optDigest() {
      return !this.digest ? null :
      	(this.digest == this.digested ? '(' + this.digest + ')' : '(Invalid:' + this.digest + ')')
    }
  },
//  methods: {
//  },
  created() {
    this.top = new TopHandler(this)
  },
  mounted() {
    let loc = window.location
      , url = loc.origin + '/json' + loc.search
//console.log("Fetch:", url)
    Wylib.Common.ajax(url, data => {
      let tmpDoc = Object.assign({}, data)
      delete tmpDoc.digest
      let strung = Stringify(tmpDoc)
console.log("Str:", strung)
      this.digested = Hash.sha256().update(strung).digest('hex')

console.log("Got:", JSON.stringify(data))
      ;['tag','title','text','sections'].forEach(t=>{
        this.state[t] = data[t]
      })
      this.key = [data.domain, data.name, data.version, data.language].join('-')
      this.digest = data.digest.replace(/^\\x/,'')

console.log("Digest:", this.digest)
console.log("Computed:", this.digested)
    })
  },
})
