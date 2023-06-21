//Save user's profile photo to DB
//Copyright MyCHIPs.org; See license in root of this package
// ----------------------------------------------------------------------------
//TODO:
//- Receive a photo file from the frontend
//- Scale it to a pre-determined sie
//-
const { log } = require('./common')
const Sharp = require('sharp')

// ----------------------------------------------------------------------------

function photo(info, cb, resource) {
  if (resource) return false			//No support for http calls

  let {data, view, db} = info
    , {fields, options} = data
    , error, content
    , max = options?.max ?? 512
    , fData = fields?.file_data
    , fileData = Buffer.isBuffer(fData) ? fields.fData :	//Make sure we have a buffer type
      (typeof fData == 'object' && fData.type == 'Buffer') ? Buffer.from(fData.data) : null
      
log.debug('File photo:', max, Object.keys(fields), typeof fileData)
log.debug('  fmt:', fields.file_fmt, 'cmt:', fields.file_cmt)
log.debug('  data:', Object.keys(fields.file_data), 'l:', fileData.length, 'd:', fileData)

  Sharp(fileData)	// Resize the image to have a height and width of at least 512px
    .resize(max, max, {
      fit: 'outside'
    })
    .toBuffer({ resolveWithObject: true })
    .then(({ data, info }) => {

      const left = Math.max(0, (info.width - max) / 2);	// How much to crop?
      const top = Math.max(0, (info.height - max) / 2);
log.debug(' left:', left, 'top:', top)

      return Sharp(data)		// Crop the image
        .extract({ left: Math.floor(left), top: Math.floor(top), width: max, height: max })
        .toBuffer();
    })
    .then(imageData => {		// Store to DB
      let parms = [
        fields.file_type ?? 'photo', 
        fields.file_fmt ?? 'image/jpeg',
        fields.file_cmt ?? 'Profile', 
        imageData
      ]
      , sql = `insert into mychips.file_v_me
        (file_type, file_fmt, file_cmt, file_data) values ($1, $2, $3, $4)
        returning *`
log.debug(' sql:', sql)
      return db.query(sql, parms)
    })
    .then(res => {
      content = res?.rows[0]
      cb(null, content)
    })
    .catch(error => {
      log.error('During image processing:', error.message);
      cb(error, null)
    });

  return false
}

module.exports = {
  'mychips.file_v_me': {photo}
}
