//Admin interface; Edit a single User's data
//Copyright MyCHIPs.org: GNU GPL Ver 3; see: License in root of this package
// -----------------------------------------------------------------------------
// TODO:
//- Obsolete, remove (after grabbing modal model)
//- 

<template>
  <transition name="modal">
    <div class="modal-mask">
      <div class="modal-wrapper">
        <div class="modal-container">

          <div class="modal-header">
            <slot name="header">
              Editing: {{uid}}
            </slot>
          </div>

          <div class="modal-body">
            <slot name="body">
              Body to edit: {{uid}}
              <table>
                <tr v-for="attr in Object.keys(userData)">
                  <td>{{attr}}</td>
                  <td><input type=text v-model:"userData[attr]"/></td>
                </tr>
              </table>
            </slot>
          </div>

          <div class="modal-footer">
            <slot name="footer">
              <span >
                <button @click="$emit('close')">Cancel</button>
                <button @click="save()">Save</button>
                <button class="modal-default-button"@click="save(); $emit('close')">OK</button>
              </span>
            </slot>
          </div>
        </div>
      </div>
    </div>
  </transition>
</template>

<style>
  .modal-mask {
    position: fixed;
    z-index: 9998;
    top: 0;
    left: 0;
    width: 100%;
    height: 100%;
    background-color: rgba(0, 0, 0, .2);
    display: table;
    transition: opacity .4s ease;
  }

  .modal-wrapper {
    display: table-cell;
    vertical-align: middle;
  }

  .modal-container {
    border: 1px solid blue;
    width: 300px;
    margin: 0px auto;
    padding: 20px 30px;
    background-color: #f8f8f8;
    border-radius: 4px;
    box-shadow: 0 2px 8px rgba(0, 0, 0, .33);
    transition: all .3s ease;
    font-family: Helvetica, Arial, sans-serif;
  }

  .modal-header h3 {
    margin-top: 0;
    color: #42b983;
  }

  .modal-body {
    margin: 20px 0;
  }

  .modal-default-button {
    float: right;
  }

  .modal-enter {
    opacity: 0;
  }

  .modal-leave-active {
    opacity: 0;
  }

  .modal-enter .modal-container, .modal-leave-active .modal-container {
    -webkit-transform: scale(1.1);
    transform: scale(1.1);
  }
</style>

<script>
var siteSocket = require('../common/SiteSocket')

export default {
  data() { return {
    myValue: false,
    userData: {
      name: 'Fred',
      user_cdi: 'addr',
      user_hid: 'hid'
    }
  }},
  props: ['uid'],
  methods: {
    save() {
      console.log('Saving record for: ' + this.uid)
    }
  },
  watch: {
    uid: function () {
      console.log('Launching UserEdit on uid: ' + this.uid)
      siteSocket.listen('user_rec:' + this.uid, (data) => {
        console.log("Data back from user_rec:" + JSON.stringify(data))
        this.userData = data
      })
    }
  }
}
</script>
