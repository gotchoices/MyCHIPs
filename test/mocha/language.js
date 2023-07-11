//Test language data dictionary
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
// TODO
//- 
const Fs = require('fs')
const Path = require('path')
const Child = require('child_process')
const assert = require("assert");
const { DBName, DBAdmin, testLog, Schema, SchemaDir, dbClient } = require('./common')
var log = testLog(__filename)
const dbConfig = {database:DBName, user:DBAdmin, connect:true, log, schema:Schema}
const SchemaList = "'mychips','json'"
const languages = ['fin', 'spa', 'nep', 'xyz']
var missing = []

describe("Language data dictionary tests", function() {
  var db
  
  before('Connect to (or create) test database', function(done) {
    this.timeout(4000)		//May take a while to build database
    db = new dbClient(dbConfig, (chan, data) => {}, done)
  })

  it('Check for undocumented tables', function(done) {
    let sql = `select * from wm.table_data td where td_sch in (${SchemaList}) and not exists
      (select * from wm.table_text tt where tt.tt_sch = td.td_sch and tt.tt_tab = td.td_tab and tt.language = 'eng') order by 1,2`
//log.debug("Sql:", sql)
    db.query(sql, (e, res) => {if (e) done(e)		//log.debug("rows:", res.rows ? JSON.stringify(res.rows) : null)
      let objs = res.rows.map(el => (el.obj))
        , list = res.rows.length > 0 ? JSON.stringify(objs,null,2) : ''
      assert.equal(list, '')
//      assert.equal(res.rows.length, 0)
      done()
    })
  })

  it('find stray text for non-existent tables/views', function(done) {
    let sql = `select * from wm.table_text tt where not exists (
      select * from wm.table_lang tl where tl.sch = tt.tt_sch and tl.tab = tt.tt_tab)
      and tt.tt_sch in (${SchemaList})`
log.debug("Sql:", sql)
    db.query(sql, (e, res) => {if (e) done(e)
log.debug("res:", res)
      assert.equal(res.rows.length, 0)
      done()
    })
  })

  it('Check for undocumented columns', function(done) {
    let sql = `select sch,tab,col from wm.column_lang where help is null and sch in (${SchemaList}) and language = 'eng' order by 1,2`
//log.debug("Sql:", sql)
    db.query(sql, (e, res) => {if (e) done(e)
      let objs = res.rows.map(el => (el.sch + '.' + el.tab + '.' + el.col))
        , list = res.rows.length > 0 ? JSON.stringify(objs,null,2) : ''
log.debug("res:", res, "Rows:", JSON.stringify(res?.rows))
      assert.equal(list, '')
//      assert.equal(res.rows.length, 0)
      done()
    })
  })

  it('find stray text for non-existent columns', function(done) {
    let sql = `select * from wm.column_text ct where not exists (
      select * from wm.column_lang cl 
        where cl.sch = ct.ct_sch and cl.tab = ct.ct_tab and cl.col = ct.ct_col)
      and ct.ct_sch in (${SchemaList})`
log.debug("Sql:", sql)
    db.query(sql, (e, res) => {if (e) done(e)
//log.debug("res:", res, "Rows:", JSON.stringify(res?.rows))
      assert.equal(res?.rows?.length, 0)
      done()
    })
  })

  function checkLanguage(lang) {
    it(`Check for untranslated tags in: ${lang}`, function(done) {
    
    let fields = ['fr_lang','fr_title','fr_help','language','title','help','sch','tab','type','col','tag']
      , where = `fr_lang = 'eng' and language = '${lang}' and (help isnull or title isnull)`
      , order = 'order by sch, tab, type, col, tag'
      , sql = `select ${fields.join(',')} from wm.language where ${where} ${order}`
log.debug("Sql:", sql)
      db.query(sql, (e, res) => {if (e) done(e)
        rows = res?.rows
log.debug("res:", res, 'rows:', rows.length)
        if (rows.length > 0) {			//If missing items found, create CSV file of results
          let format = require('@fast-csv/format').format
            , stream = format()
            , file = Path.join(__dirname, `lang-${lang}.csv`)
            , writable = Fs.createWriteStream(file)
log.debug("file:", file)
          stream.pipe(writable)
          stream.write(fields)			//Header row
          rows.forEach(row => {
            row.language = lang
            stream.write(row)
          })
          stream.end()
        }
        missing.push(lang)			//Remember if errors were found in this language
//        assert.equal(rows?.length, 0)
        done()
      })
    })
  }

/* Disable for now 
  it('Install languages', function(done) {
    Child.exec("wyseman lang", {
      cwd: SchemaDir,
      env: Object.assign({}, process.env, {MYCHIPS_DBNAME: DBName})
    }, (e,out,err) => {
      if (e) done(e); done()
    })
  })

  languages.forEach(lang => {
    checkLanguage(lang)
  })

  it(`Reporting on missing language tags: ${missing}`, function(done) {
log.debug("Missing tags in:", missing)
    assert.equal(missing.length, 0)
  })

/* */
  after('Disconnect from test database', function(done) {
    db.disconnect()
    done()
  })
})
