//User client, main component
//Copyright MyCHIPs.org: GNU GPL Ver 3; see: License in root of this package
// -----------------------------------------------------------------------------
// TODO:
//- 
<template>
  <div id="app">
    <router-link to="/">Home</router-link>
    <router-link to="/peers">Partners</router-link>
    <router-link to="/config">Settings</router-link>
    <router-view/>
  </div>
</template>

<script>
export default {
}
</script>

<style>
#app {
}
</style>
