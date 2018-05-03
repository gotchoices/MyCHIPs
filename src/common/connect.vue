//Admin interface; Home, connection screen
//Copyright MyCHIPs.org: GNU GPL Ver 3; see: License in root of this package
// -----------------------------------------------------------------------------
// TODO:
//- Has to be independent of database, wylib
//- 

Depricated

<template>
  <div class="wylib-connect" v-if="state.posted">
    <div class="header" title="Keeps a list of servers you normally connect to">My Servers:</div>
    <table>
      <tbody>
        <tr>
          <td><input v-model:value="newSite" v-on:keyup.13="addSite(newSite)" title="Type in the URL (domain:port) of the server you want to connect to"/></td>
          <td><button @click="addSite(newSite)" title="Add a new server URL to my list">Add</button></td>
        </tr>
        <tr v-for="site in sites">
          <td>{{ site }}</td>
          <td><button @click="connectSite(site)" title="Manage MyCHIPs server at this URL">Connect</button></td>
          <td><button @click="removeSite(site)" title="Remove this server from my list">Forget</button></td>
        </tr>
      </tbody>
    </table>
  </div>
</template>

<script>
import Wylib from 'wylib'

export default {
  props: {
    state:	null,
    siteKey:	'wylib_sites',
  },
  data() { return {
    newSite: '',
    sites: []
  }},
  methods: {
    connectSite(addr) {		//Force connection to a specified site
console.log("Connecting to: " + addr)
      Wylib.Wyseman.connect(addr)
    },
    addSite(addr) {		//Add favorite site to our list
console.log("Add: " + addr)
      if (addr != '' && (this.sites.length == 0 || this.sites.indexOf(addr) < 0))
        this.sites.push(addr)
      localStorage.setItem(this.siteKey, JSON.stringify(this.sites))
    },
    removeSite(addr) {		//Remove site from our favorites list
console.log("Remove: " + addr)
      this.sites.splice(this.sites.indexOf(addr),1)
      localStorage.setItem(this.siteKey, JSON.stringify(this.sites))
    }
  },

  beforeMount: function() {
    Wylib.Com.react(this.state, {posted: false})
  },

  mounted: function () {	//When this GUI element is activated
//console.log("Mounted:", this.sites)
    this.$nextTick(function () {
      if (localStorage[this.siteKey])	//Get our list of favorites
        this.sites = JSON.parse(localStorage.getItem(this.siteKey))
        
      let suggested = window.location.hostname + ":54321"
      if (this.sites.length == 0 || this.sites.indexOf(suggested) < 0)
        this.newSite = suggested	//Offer a resonable default to connect to
//console.log("newSite:", this.newSite)
    })
  }
}
</script>

<style lang='less'>
.wylib-connect {
}
.wylib-connect .header {
  padding: 4px;
}
</style>
