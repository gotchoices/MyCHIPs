//Admin interface; Users data
//Copyright MyCHIPs.org: GNU GPL Ver 3; see: License in root of this package
// -----------------------------------------------------------------------------
// TODO:
//- Report errors on file import
//- 
import Wylib from 'wylib'

module.exports = function(ev) {
  let i, f; for (let i = 0, f; f = ev.target.files[i]; i++) {
    let reader = new FileReader();
    reader.onload = ()=>{
      let jdat = reader.result		//JSON.stringify(reader.result)
//console.log("Jdat:" + jdat)
      let spec = {view: 'json.import(jsonb)', params: [jdat]}
      Wylib.Wyseman.request('users.import.'+this._uid, 'tuple', spec, (res, err) => {
        if (err) this.top().error(err)
//console.log("Import res:", res)
      })
    }
    reader.readAsText(f)
  }
  setTimeout(()=>{ev.target.value = null}, 1500)
}
