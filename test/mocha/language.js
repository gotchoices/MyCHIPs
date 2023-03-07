//Test language data dictionary
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
// TODO
//- 
const Fs = require('fs')
const assert = require("assert");
const { DBName, DBAdmin, testLog, Schema, dbClient } = require('./common')
var log = testLog(__filename)
const dbConfig = {database:DBName, user:DBAdmin, connect:true, log, schema:Schema}
const SchemaList = "'mychips','json'"
const languages = ['fin', 'spa']
var missing = []

describe("General schema tests", function() {
  var db
  
  before('Connect to (or create) test database', function(done) {
    this.timeout(4000)		//May take a while to build database
    db = new dbClient(dbConfig, (chan, data) => {}, done)
  })

  it('Check for undocumented tables', function(done) {
    let sql = `select sch,tab from wm.table_lang where help is null and sch in (${SchemaList}) order by 1,2`
//log.debug("Sql:", sql)
    db.query(sql, (e, res) => {if (e) done(e)
//log.debug("res:", res.rows ? JSON.stringify(res.rows) : null)
      assert.equal(res.rows.length, 0)
      done()
    })
  })

  it('Check for undocumented columns', function(done) {
    let sql = `select sch,tab,col from wm.column_lang where help is null and sch in (${SchemaList}) order by 1,2`
log.debug("Sql:", sql)
    db.query(sql, (e, res) => {if (e) done(e)
//log.debug("res:", res)
      assert.equal(res.rows.length, 0)
      done()
    })
  })

  function checkLanguage(lang) {
    it(`Check for untranslated tags in: ${lang}`, function(done) {
    
    let fields = ['fr_lang','fr_title','fr_help','to_lang','title','help','sch','tab','type','col','tag']
      , where = `fr_lang = 'eng' and (to_lang isnull or to_lang = '${lang}') and (help isnull or title isnull)`
      , sql = `select ${fields.join(',')} from wm.language where ${where}`
log.debug("Sql:", sql)
      db.query(sql, (e, res) => {if (e) done(e)
log.debug("res:", res)
        rows = res?.rows
        if (rows.length > 0) {			//If missing items found, create CSV file of results
          let format = require('@fast-csv/format').format
            , stream = format()
            , file = `lang-${lang}.csv`
            , writable = Fs.createWriteStream(file)
          stream.pipe(writable)
          stream.write(fields)			//Header row
          rows.forEach(row => stream.write(row))
          stream.end()
        }
        missing.push(lang)			//Remember if errors were found in this language
//        assert.equal(rows?.length, 0)
        done()
      })
    })
  }

/* Disable for now  
  languages.forEach(lang => {
    checkLanguage(lang)
  })

  it(`Reporting on missing language tags: ${missing}`, function(done) {
    assert.equal(missing.length, 0)
  })

/* */
  after('Disconnect from test database', function(done) {
    db.disconnect()
    done()
  })
})