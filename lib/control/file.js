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
    , max = options.max ?? 512
  log.debug('File photo', options)

  Sharp(fields.file_data)	// Resize the image to have a height and width of at least 512px
    .resize(max, max, {
      fit: 'outside'
    })
    .toBuffer({ resolveWithObject: true })
    .then(({ data, info }) => {

      const left = Math.max(0, (info.width - max) / 2);	// How much to crop?
      const top = Math.max(0, (info.height - max) / 2);

      return Sharp(data)		// Crop the image
        .extract({ left: Math.floor(left), top: Math.floor(top), width: max, height: max })
        .toBuffer();
    })
    .then(imageData => {		// Store to DB
      let parms = [
        fields.file_seq, 
        fields.file_type ?? 'photo', 
        fields.file_fmt ?? 'image/jpeg',
        fields.file_cmt ?? 'Profile', 
        imageData
      ]
      , sql = `insert into mychips.file_v_me
        (file_ent, file_seq, file_type, file_fmt, file_cmt, file_data)
        values (base.user_id(session_user), $1, $2, $3, $4, $5)
        on conflict (file_ent, file_seq) do update
        set file_type = $2, file_fmt = $3, file_cmt = $4,file_data = $5
        returning *`
      return db.query(sql, parms)
    })
    .then(res => {
      content = res?.rows[0]
      cb(null, content)
    })
    .catch(error => {
      console.error('During image processing:', error);
      cb(error, null)
    });

  return false
}

module.exports = {
  'mychips.file_v_me': {photo}
}
