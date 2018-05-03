//Document viewer
//Copyright MyCHIPs.org: GNU GPL Ver 3; see: License in root of this package
// -----------------------------------------------------------------------------
// TODO:
//- 
console.log("Location:", document.location)
const getParms = function(query) {
  if (!query) {return {}}
  return (/^[?#]/.test(query) ? query.slice(1) : query)
    .split('&')
    .reduce((parms, parm) => {
      let [ key, value ] = parm.split('=');
      parms[key] = value ? decodeURIComponent(value.replace(/\+/g, ' ')) : '';
      return parms;
    }, {});
};

var parms = getParms(document.location.search)
console.log("Parms:", parms)
var address = parms.sock || 'lux3:3001'			//Fixme
address = 'ws:/' + address

var webSock = new WebSocket(address)
webSock.addEventListener('error', event => {
  console.log("Error connecting to site:", address)
})

webSock.addEventListener('close', event => {
  console.log("Connection closed to:", address)
})

webSock.addEventListener('open', event => {
  console.log("Connected to backend: " + address)

  webSock.addEventListener('message', ev => {
    let pkt = JSON.parse(ev.data)
    console.log("Message from backend: " + pkt)
  })
})

var container = document.getElementById('docFrame')
container.setAttribute('width', '100%')
//container.setAttribute('height', '100%')
container.type='application/pdf'
container.src='testdoc.pdf'
