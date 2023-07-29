//For build a pdfmake control json from a contract document and rendering it to PDF
//Copyright MyCHIPs.org; See license in root of this package
// ----------------------------------------------------------------------------
//TODO:
//X- Make module into a class with constructor
//X- Can build contract pdf
//- Can build tally prelude
//- Can build tally postlude
//- Pages 2+ have descriptive header
//- Can control paper size
//- 
var PdfPrinter = require('pdfmake')
const Stream = require('stream')
const Fs = require('fs')

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
};

var printer = new PdfPrinter(fonts)

var docTemplate = {
  pageSize: 'Letter',
  defaultStyle: {
    font: 'Helvetica',
    fontSize: 12
  },
  styles: {
    header: {
      fontSize: 18,
      bold: true
    },
    subhead: {
      fontSize: 12,
    },
    subscript: {
      fontSize: 6,
      alignment: 'right'
    },
    par: {
      fontSize: 12,
      margin: [0, 0, 0, 10]
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

module.exports = class {
  constructor(log) {
    this.log = log
  }

  textTable(body) {
    return {
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

  contSection(contract, prefix = '') {	//Returns one or more elements of a table body array
    let {host, name, version, language, title, text, rid, sections} = contract
      , content = []			//;this.log.debug('APdf:', JSON.stringify(data,null,2))
      , docID = ''
      , docSpec = ''
      , style = prefix ? 'subhead' : 'header'

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
      content.push([{text:prefix}, {text,style: 'par'}])
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

  contract (data, cb) {			//Format a structured document
    let body = this.contSection(data)
      , content = this.textTable(body)
//Fs.writeFileSync('local/tmp-out.json', JSON.stringify(content,null,2))
//content = JSON.parse(Fs.readFileSync('local/tmp-in.json'))
    let docDef = Object.assign({content}, docTemplate)
    this.render(docDef, cb)
  }
    
  render(docDefinition, cb) {
    let doc = printer.createPdfKitDocument(docDefinition)
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
  }
}	//class
