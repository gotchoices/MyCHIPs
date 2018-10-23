#Main classes for mychips site
#TODO:
#- Allow for other types (stock, foil, query) of tickets
#- Get user port(s) from parms, if exists
#- Get user inet address from parms, if exists
#- 
#- 
require 'json'
require 'openssl'
require 'mychips/db'

module MyCHIPs

class User
# -----------------------------------------------------------------------------
  def initialize(source)

printf("Init User from:%s (%s)\n", source, source.class)
    if source =~ URI::regexp		#Is this a URL?
#      @data = Oj.load(Net::HTTP.get(URI(source)))
      @data = JSON.load(Net::HTTP.get(URI(source)))
    elsif File::exist?(source)		#Is this a file?
#      Oj.default_options = {mode: :compat}
#      @data = Oj.load(File.read(source))
      @data = JSON.load(File.read(source))
    else
      db = DB.new()
      res = db.doSelect('*','mychips.users_v',Hash['peer_cdi',source])	#Search by CHIPs ID
      if res.ntuples <= 0 && /\A\d+\z/.match(source)
        res = db.doSelect('*','mychips.users_v',Hash['id',source])	#Search by entity ID
      end
      raise "Can't find user: #{source}" if res.ntuples <= 0
      @data = Hash['user',res[0]]
    end
  end

  def [](x)		#Fetch named hash elements
    @data['user'][x]
  end

# -------------------------------------------------------------------
  def store(force = false)		#Load this user into the database
    if !force
      #Fixme: check for similar records in entities/users
    end
    raise "File: #{source} is not valid JSON user data" if !@data['user']
    DB.new().import(@data)[0]		#Return ID
  end

# -------------------------------------------------------------------
  def export(fname)
  end
end	#class User

# -----------------------------------------------------------------------------
class Ticket
  def initialize(uid)
    user = User.new(uid)
    id = user['id']
printf("user:%s id:%s\n", user.class, id)
puts 'user:' + user.to_s + ' id:' + id.to_s

    @db = DB.new()
    @ticket = @db.doInsert('mychips.tokens_v', Hash['token_ent'=>id, 'allows'=>'user'])

    upd = Hash[]
    upd['user_port'] = @db.getParm('user_port') if !user['user_port']	#Use default values if this user doesn't have an address and port defined
    upd['user_inet'] = @db.getParm('user_inet') if !user['user_inet']
    @db.doUpdate('mychips.users_v', upd, Hash['id',id]) if upd.length > 0
#printf("private:%s\n", key.to_pem)

    @jdata = @db.export('ticket', Hash['id',@ticket['token_ent'],'seq',@ticket['token_seq']])
    @ticket = JSON.parse(@jdata)['ticket']	#Grab again from db to get any auto-generated values
  end
  
# -----------------------------------------------------------------------------
  def save(fname)			#Save this ticket to a file
    File.open(fname, 'w') { |file| file.write(@jdata) }
  end

# -----------------------------------------------------------------------------
  def display()				#Display barcode of the ticket
    require 'tk'
    require 'barby'
    require 'barby/barcode/qr_code'
    require 'barby/outputter/png_outputter'
    
    bcode = Barby::QrCode.new(@jdata)
    (root = TkRoot.new).title = "Ticket Preview"
    ping = TkPhotoImage.new(data:bcode.to_png(xdim:1), format:'png')
    TkLabel.new(root,text:'Ticket:' + @ticket['token']).pack(side:'top',anchor:'w')
    TkLabel.new(root,text:'Expires:' + @ticket['expires']).pack(side:'top',anchor:'w')
    TkLabel.new(root,image:ping).pack(side:'top')
    TkButton.new(root,text:'Dismiss').pack(side:'bottom',fill:'x').command {
      root.destroy
    }
    Tk.mainloop
  end

end	#class Ticket

class Certificate < OpenSSL::X509::Certificate
# -----------------------------------------------------------------------------
  def initialize(id=nil, force=false)
    @db = DB.new()
    siteid = @db.getParm('site_ent')
    name = userData(@id = id ||= siteid)	#Get info from DB about this user
#printf "name:%s\n", name

    if !force && @udat['user_crt']		#Is there already a valid certificate in the DB?
      super(@udat['user_crt'])
      return if Time.now < self.not_after	#Use if if it is still good
    end

    super()					#Create a certificate on the fly
    self.version = 2
    self.serial = 1				#Fixme: should this increment?
    self.not_before = Time.now
    self.not_after  = Time.now + (24 * 3600 * @db.getParm('cert_days').to_i)
    self.subject = OpenSSL::X509::Name.new(name)
    self.public_key = OpenSSL::PKey::RSA.new(@udat['user_pub'])

    self.issuer = OpenSSL::X509::Name.new((id == siteid) ? name : userData(siteid))
    key = OpenSSL::PKey::RSA.new(@db.getParm('site_prv'))
    self.sign key, OpenSSL::Digest::SHA256.new	#Sign the user's certificate
#puts cert.to_text
    res = @db.doUpdate('mychips.users_v',Hash['user_crt',self.to_pem],"id=#{id}")
  end	#initialize

# -------------------------------------------------------------------
  def userData(id)				#Get and parse info about user from database
#printf "userData id:%s\n", id
    res = @db.doSelect('peer_cdi,ent_type,ent_name,giv_name,fir_name,pref_name,title,std_name,born_date,phone_comm,cell_comm,email_comm,web_comm,ship_addr,ship_city,ship_state,ship_pcode,ship_country','mychips.users_v_flat',"id=#{id} and not ent_inact")
    raise "Can't find data for contact #{id}" if res.ntuples != 1
    @udat = res[0]				#Get results in a hash
#p @udat
    if @udat['ent_type'] == 'p'			#The site is a person
      flds = %w{CN=user_cdi GN=fir_name initials=fir_name name=pref_name generationQualifier=born_date title=title emailAddress=email_comm serialNumber=phone_comm serialNumber=cell_comm SN=ent_name O=std_name description=user_cmt OU=ship street=ship_addr L=ship_city ST=ship_state postalCode=ship_pcode C=ship_country}
    else
      flds = %w{CN=user_cdi dnQualifier=web_comm O=ent_name generationQualifier=born_date emailAddress=email_comm serialNumber=phone_comm OU=ship street=ship_addr L=ship_city ST=ship_state postalCode=ship_pcode C=ship_country}
    end
    ary = flds.collect { |ea|			#Build array of entity information
      k,f = ea.split('=',2)
      if !@udat.key?(f)				#If its not in the query result
        [k, f]					#Supply a dummy value
      elsif @udat[f]				#If its non-null
        [k, @udat[f] || 'null']
      else
        nil
      end
    }.compact
    return ary
  end

# -------------------------------------------------------------------
  def context()					#Create a context using this certificate, and our site key

#Fixme: Is any of this necessary?
#p OpenSSL::SSL::SSLContext::DEFAULT_PARAMS	#https://gist.github.com/tam7t/86eb4793e8ecf3f55037
#OpenSSL::SSL::SSLContext::DEFAULT_PARAMS[:options] |= OpenSSL::SSL::OP_NO_SSLv2
#OpenSSL::SSL::SSLContext::DEFAULT_PARAMS[:options] |= OpenSSL::SSL::OP_NO_SSLv3
#OpenSSL::SSL::SSLContext::DEFAULT_PARAMS[:ssl_version] ="TLSv1"
#p OpenSSL::SSL::SSLContext::METHODS		#Available versions

    context = OpenSSL::SSL::SSLContext.new
    context.cert = self
    context.key = OpenSSL::PKey::RSA.new(@db.getParm('site_prv'))
    context.ssl_version = :TLSv1
    context.verify_mode = OpenSSL::SSL::VERIFY_PEER
    (context.cert_store = OpenSSL::X509::Store.new).add_cert self	#We are the CA for the client
    return context
  end	#context

end	#class Certificate
end	#module MyCHIPs
