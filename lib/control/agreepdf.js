//var pdfMake = require('pdfmake/build/pdfmake.js');
//var pdfFonts = require('pdfmake/build/vfs_fonts.js');
//pdfMake.vfs = pdfFonts.pdfMake.vfs;
//console.log("F:", pdfFonts)

var PdfPrinter = require('pdfmake')
const Stream = require('stream')

var fonts = {
//  Courier: {
//    normal: 'Courier',
//    bold: 'Courier-Bold',
//    italics: 'Courier-Oblique',
//    bolditalics: 'Courier-BoldOblique'
//  },
  Helvetica: {
    normal: 'Helvetica',
    bold: 'Helvetica-Bold',
    italics: 'Helvetica-Oblique',
    bolditalics: 'Helvetica-BoldOblique'
  },
//  Times: {
//    normal: 'Times-Roman',
//    bold: 'Times-Bold',
//    italics: 'Times-Italic',
//    bolditalics: 'Times-BoldItalic'
//  },
//  Symbol: {
//    normal: 'Symbol'
//  },
//  ZapfDingbats: {
//    normal: 'ZapfDingbats'
//  }
};

var printer = new PdfPrinter(fonts)

var docDefinition = {
    content: [
        {
            text: 'Main Title',
            style: 'header'
        },
        'First paragraph',
        'Another paragraph, this time a little bit longer to make sure, this line will be divided into at least two lines',
        {
            text: 'Subheader 1',
            style: 'subheader'
        },
        'Sub-paragraph',
        {
            text: 'Subheader 2',
            style: 'subheader'
        },
        'Another sub-paragraph',
//        {
//            image: 'path-to-your-image.jpg',
//        }
    ],
    defaultStyle: {
      font: 'Helvetica'
    },
    styles: {
        header: {
            fontSize: 18,
            bold: true,
            margin: [0, 0, 0, 10]
        },
//        subheader: {
//            fontSize: 16,
//            bold: true,
//            margin: [0, 10, 0, 5]
//        },
//        paragraph: {
//            fontSize: 12,
//            margin: [0, 5, 0, 5]
//        }
    }
};

module.exports = function(log, cb) {
  try {
    const chunks = [];
    const doc = printer.createPdfKitDocument(docDefinition)
    
      doc.on('end', () => {			//console.log('End')
        const pdfBuffer = Buffer.concat(chunks);
        cb(null, pdfBuffer);
      })
      .on('data', (chunk) => {			//console.log('Chunk')
        chunks.push(chunk)
      })
      .on('error', (err) => {			//console.log('Err:', err)
        log.error('Reading PDF Stream: ' + err)
        cb(err)
      })
      doc.end()
      
  } catch (err) {
    log.error('Generating agreement PDF: ' + err)
    cb(err)
  }
}
