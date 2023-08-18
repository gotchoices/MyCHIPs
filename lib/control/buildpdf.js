//For build a pdfmake control json from a contract document and rendering it to PDF
//Copyright MyCHIPs.org; See license in root of this package
// ----------------------------------------------------------------------------
//TODO:
//- Pages 2+ have descriptive header
//- Can control paper size
//- 
var PdfPrinter = require('pdfmake')
const Stream = require('stream')
const Fs = require('fs')
const Flat = require('flat')
const Qr = require('qr-image')
const vSpace = 8

var fonts = {
  Courier: {
    normal: 'Courier',
    bold: 'Courier-Bold',
    italics: 'Courier-Oblique',
    bolditalics: 'Courier-BoldOblique'
  },
  Helvetica: {
    normal: 'Helvetica',
    bold: 'Helvetica-Bold',
    italics: 'Helvetica-Oblique',
    bolditalics: 'Helvetica-BoldOblique'
  },
  Times: {
    normal: 'Times-Roman',
    bold: 'Times-Bold',
    italics: 'Times-Italic',
    bolditalics: 'Times-BoldItalic'
  },
}

var docTemplate = {
  pageSize: 'Letter',
  defaultStyle: {
    font: 'Helvetica',
    fontSize: 12
  },
  styles: {		//Put margin spacing at bottom of objects [L, T, R, B]
    header: {
      fontSize: 16,
      bold: true,
      margin: [0, 0, 0, vSpace]
    },
    midhead: {
      fontSize: 11
    },
    subhead: {
      fontSize: 8
    },
    subscript: {
      fontSize: 6,
      alignment: 'right'
    },
    par: {
      fontSize: 10,
      margin: [0, 0, 0, vSpace]
    },
    subpar: {
      fontSize: 8
    }
  },
  footer: function(curPage, pgCount) {
    if (pgCount > 1) return {
      text: curPage.toString() + ' / ' + pgCount,
      alignment: 'right',
      margin: [0, 0, 40, 20]
    }
  }
}

module.exports = class {	//PDF builder class
  constructor(log) {
    this.log = log
    this.printer = new PdfPrinter(fonts)
    this.init()
  }

  init() {			//Start out with a blank document
    this.content = []
  }

  add(chunk) {			//Add a chunk to the document
    if (Array.isArray(chunk))
      chunk.forEach(ch => this.content.push(ch))
    else if (chunk) this.content.push(chunk)
    return this
  }

  textTable(body, indent = 0) {		//Wrap the provided body columns in a table
    let margin = [indent, 0, 0, vSpace]
    if (!(body?.length >= 1)) return {}
    return {margin,
      table: {
        widths: ['auto', '*'],
        body,
      },
      layout: {
        noBorders: true,
        hLineWidth: () => 0,	//set both to 1 for debug
        vLineWidth: () => 0,
        paddingLeft: (i, node) => 0,
        paddingRight: (i, node) => 2,
        paddingTop: (i, node) => 0,
        paddingBottom: (i, node) => 2
      }
    }
  }

  compTitle(lang, eng, indent = 6, style = 'midhead', substyle = 'subhead') {//Title block with description
    let margin = [indent, 0, 0, vSpace]
    return {margin, text: [
      {
        text: (lang?.title ?? eng) + ':  ',
        style
      }, {
        text: (lang?.help ?? ''),
        style: substyle
      }
    ]}
  }

  termsSection(terms) {			//Returns formatted credit terms section
    let flatTerms = Flat(terms)
      , content = []
      , style = 'subpar'
    if (terms && flatTerms) Object.keys(flatTerms).forEach(key => {
      content.push([
        {text: key, style}, {text: flatTerms[key], style}
      ])
    })
    if (content.length <= 0) content.push(["-"])
    return content
  }

  certSection(cert, uTags) {		//Returns formatted certificate section
    let flatCert = cert ? Flat(cert) : {}
      , style = 'subpar'
      , content = []
      , values = uTags?.col?.cert?.values	//;this.log.debug('UT:', JSON.stringify(values,null,2))
    Object.keys(flatCert).forEach(key => {
      let keyPath = key.split('.')
        , idx = parseInt(keyPath[1]) || ''	//drop any array indexing in file, place, connect
        , lKey = (idx || idx === 0) ? 
          keyPath.slice(0, 1).concat(keyPath.slice(2)).join('.') :
          key					//, a = this.log.debug('key:', key, idx, lKey)
        , val = values.find(el => (el.value == lKey)) ?? ''
        , text = val?.title ? 
          val?.title + ' (' + key + ') ' + idx : 
          key
      content.push([
        {text, style}, 
        {text: flatCert[key], style}
      ])
    })
    if (content.length <= 0) content.push(["-"])
    return content
  }

  sigSection(data) {			//Returns formatted signature
    let { tally, langTags } = data
      , { foil, stock, sign } = tally
      , foilKey = foil?.cert?.public
      , stockKey = stock?.cert?.public
      , foilData = {d: sign?.digest, k: foilKey, s: sign?.foil}
      , stockData = {d: sign?.digest, k: stockKey, s: sign?.stock}
      , foilQr = Qr.imageSync(JSON.stringify(foilData), {type:'png'})?.toString('base64')
      , stockQr = Qr.imageSync(JSON.stringify(stockData), {type:'png'})?.toString('base64')
      , lTttv = langTags?.col?.tally_type?.values ?? []
      , foilTitle = (lTttv.find(el => (el.value == 'foil')).title ?? 'Foil') + ':'
      , stockTitle = (lTttv.find(el => (el.value == 'stock')).title ?? 'Stock') + ':'
      
//this.log.debug('fD:', JSON.stringify(foilData))
//this.log.debug('png:', foilQr)
//this.log.debug('lD:', JSON.stringify(langTags?.col?.tally_type))
    return [
      [
        {text: foilTitle},
        {text: stockTitle}
      ], [
        {text: sign.foil ?? '-'},
        {text: sign.stock ?? '-'}
      ], [
        {image: `data:image/png;base64,${foilQr}`},
        {image: `data:image/png;base64,${stockQr}`},
      ]
    ]
  }

  otherSection(data) {		//Returns formatted misc section
    let { langTags } = data
      , content = []
      , style = 'subpar'
      , item = (tag, eng) => {return [
        {
          text: (langTags.col?.[tag]?.title ?? eng) + ':',
          style
        }, {
          text: data[tag],
          style
        }
      ]}
    content.push(item('tally_uuid', 'UUID'))
    content.push(item('version', 'Version'))
    content.push(item('tally_date', 'Date'))
    content.push(item('digest', 'Digest'))
    content.push(item('comment', 'Comments'))
    return content
  }

  contSection(contract, prefix = '') {	//Returns one or more elements of a table body array
    let {host, name, version, language, title, text, rid, sections} = contract
      , content = []			//;this.log.debug('APdf:', JSON.stringify(data,null,2))
      , docID = ''
      , docSpec = ''
      , style = prefix ? 'midhead' : 'header'

    if (rid) {				//contract has a resource ID
      docSpec = (host ? host : '') +
        (name ? ':' + name : '') +
        (version ? '.' + version : '') +
        (language ? '.' + language : '')
      if (!title) title = name		//Force a title
    }

    if (title) {
      let titleBlock = this.textTable([
        [
         {text: title, style, rowSpan: 2},
         {text: docSpec, style: 'subscript'}
        ],
        [
         '',
         {text: rid, style: 'subscript'}
        ]
      ])
      content.push([{text:prefix, style}, titleBlock])
      content.push([{text:''}, {text,style: 'par'}])
    } else if (text) {
      content.push([{text:prefix, style: 'par'}, {text,style: 'par'}])
    }

    if (sections) {
      let body = []
        , count = 1
      sections.forEach(sec => {			//this.log.debug('Sec:', sec)
        let subPrefix = prefix + count + '.'
          , elements = this.contSection(sec, subPrefix)
        elements.forEach(el => body.push(el))
        count++
      })
      content.push([{text:''}, this.textTable(body)])
    }
    return content
  }

  contract (data) {			//Format a structured document to json control format
    let body = this.contSection(data)
      , content = this.textTable(body)
    return content
  }
    
  tally (data) {			//Format a tally to json control format
    let { tally, contract, langTags, userLang } = data
      , { stock, foil } = tally
//this.log.debug(tally, 'C:' + JSON.stringify(contract,null,2))
//this.log.debug('LT:', JSON.stringify(langTags?.col?.tally_type))

    this.add(this.contSection(contract))

    .add(this.compTitle(langTags.msg?.['agree.data'], 'Tally Data', 0, 'header', 'midhead'))

    .add(this.compTitle(langTags.msg?.['agree.cert.foil'], 'Foil Certificate'))
    .add(this.textTable(this.certSection(foil.cert, userLang), 10))

    .add(this.compTitle(langTags.msg?.['agree.cert.stock'], 'Stock Certificate'))
    .add(this.textTable(this.certSection(stock.cert, userLang), 10))

    .add(this.compTitle(langTags.msg?.['agree.terms.foil'], 'Foil Terms'))
    .add(this.textTable(this.termsSection(foil.terms), 10))

    .add(this.compTitle(langTags.msg?.['agree.terms.stock'], 'Stock Terms'))
    .add(this.textTable(this.termsSection(stock.terms), 10))

    .add(this.compTitle(langTags.msg?.['agree.other'], 'Other Data'))
    .add(this.textTable(this.otherSection(data), 10))

    .add(this.compTitle(langTags.msg?.['agree.sign'], 'By'))
    .add(this.textTable(this.sigSection(data), 10))

//this.log.debug('L:' + JSON.stringify(Object.keys(userLang),null,2))
//this.log.debug('M:' + JSON.stringify(userLang,null,2))
//this.log.debug('T:' + JSON.stringify(langTags.msg,null,2))
//Fs.writeFileSync('local/tmp-out.json', JSON.stringify(content,null,2))
//content = JSON.parse(Fs.readFileSync('local/tmp-in.json'))
    return this
  }	//tally
    
  render(cb) {			//Format the object's json conttent to pdf output
    let docDef = Object.assign({content: this.content}, docTemplate)
      , doc = this.printer.createPdfKitDocument(docDef)
      , chunks = []				//;this.log.debug('APdf: ', Object.keys(data))
    try {
      doc.on('end', () => {
        const pdfBuffer = Buffer.concat(chunks);
        cb(null, pdfBuffer)
      })
      .on('data', (chunk) => {
        chunks.push(chunk)
      })
      .on('error', (err) => {
        this.log.error('Reading PDF Stream: ' + err)
        cb(err)
      })
      doc.end()
        
    } catch (err) {
      this.log.error('Generating agreement PDF: ' + err)
      cb(err)
    }
    return this
  }	//render
}	//class
