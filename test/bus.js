//Message bus
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
//Allow a context to register itself to receive notification from a different async context

module.exports = function(name) {
  this.name = name
  this.clients = {}
//console.log("Bus construct", name)

  this.register = function(id, cb) {		//Clients register to receive callbacks
//console.log("Bus register:",name, id, cb)
    if (cb) 
      this.clients[id] = cb			//Register
    else if (id in this.clients && !cb)
      delete this.clients[id]			//De-register
  }
    
  this.notify = function(data) {
//console.log("Bus notify:", name, this.clients)
    Object.keys(this.clients).forEach(key => {
        this.clients[key](data)
    })
  }
}
