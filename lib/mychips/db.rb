#Open a connection to the database, managed by Wyseman library.
#Handle importing/exporting JSON records
#Copyright MyCHIPs.org: GNU GPL Ver 3; see: License in root of this package
# -----------------------------------------------------------------------------
#TODO:
#- Create view that mirrors JSON user structure exactly
#- separate schema for json import views
#- 
#- 
require 'wyseman'
require 'wyseman/db'

module MyCHIPs

# -----------------------------------------------------------------------------
class DB < Wyseman::DB
  def initialize (opts = {})
    opts[:schema] ||= File.join(File.dirname(__FILE__), '..', 'schema.sql')
    super(opts)
  end

  public
# -------------------------------------------------------------------
  def export(tag, fdat, fields={})		#Export from database in JSON format
    view = 'json.' + tag			#Form name of export view from supplied tag
    fdat.each_key {|key| fdat.delete(key) if !fields.include?(key)} if fields.length > 0

#printf("Export fdat:%s\n", fdat)
    jdat = (res = self.doSelect('*', view, fdat))[0]
    raise 'No export data found for #{fdat}' if res.ntuples <= 0
    jdat.each_key {|key| jdat.delete(key) if fdat.include?(key) or !jdat[key]}
#printf("Export:%s\n", jdat)
    JSON.pretty_generate(Hash['ticket',jdat])
  end
  
  public
# -------------------------------------------------------------------
  def import(data, keyval = nil)			#Pull JSON data from a hash into the database
    raise "Invalid JSON structure: #{data}" if !data.is_a?(Hash) || data.length != 1
    view = 'json.' + (idx0 = data.keys[0])		#Form name of import view from first key
    vals = data[idx0]					#Data is in the matching hash value
    raise "Invalid JSON data: #{vals}" if !vals.is_a?(Hash)
    kflds = self.table(view)['pkey'].gsub(/[{}]/,'').split(',')	#Get primary key field, which is not part of the JSON structure, strip off array delimiters from DB
printf("Import view:%s kflds:%s keyval:%s\n", view, kflds, keyval)

    if !keyval						#If this it a top-level object
      kflds.each { |kf| vals.delete(kf)}		#Get rid of any PK value, if it does exist
      self.x('begin;')					#If at top level, start transaction
    else
      cnt = 0
      kflds.each { |kf| 				#Assign key values from parent record
        vals[kf] = keyval[cnt]
        vals.delete(kf) if !keyval[cnt]			#Anything else gets deleted
        cnt += 1
      }
    end

    qfl, qvl = [], []
    newkey = nil
    vals.each_pair { |idx, val|
#printf("  Element:%s(%s) = %s\n", idx, val.class, val)
      if val.is_a?(String)
        qfl << self.qid(idx)				#List of sql fields
        qvl << self.quote(view,idx,val)			#List of sql values
        next						#Go on to next key/val pair
      end

      newkey = insert_gk(view,qfl,qvl,kflds) if !newkey && qfl.length > 0	#Force an insert if we got a Hash or Array

      if val.is_a?(Hash)
        import(vals[idx], newkey)			#Recursive call on one record
      elsif val.is_a?(Array)
        vals[idx].each {|v| import(v, newkey)}		#Recursive call on each element
      else
        raise "Unknown data type in JSON:#{val.class}"
      end
    }
#printf("  Post:%s newkey:%s keyval:%s\n", view, newkey, keyval)
    insert_gk(view,qfl,qvl,kflds) if !newkey && qfl.length > 0		#Do an insert if we haven't already
    self.x('commit;') if !keyval			#If at top level, commit transaction
    return newkey
  end

# -------------------------------------------------------------------
  def getParm(key, mod='mychips')			#Pull a system parameter from the database
    self.one("select base.parm('#{mod}','#{key}');")[0]
  end

# -------------------------------------------------------------------
  def setParm(key, val, mod='mychips')			#Write a system parameter to the database
    res = self.x("select base.parmsett('#{mod}','#{key}','#{esc(val)}');")
    raise "Error updating parameter: #{key}=#{val}" if res.ntuples < 1
  end

  private
# -------------------------------------------------------------------
  def insert_gk(view,flds,vals,kflds)		#Insert a record, receiving a primary key back
    sql = "insert into #{view} (#{flds.join(',')}) values (#{vals.join(',')}) returning #{kflds.join(',')};"
#printf("    SQL:%s\n",sql)
    res = self.x(sql)
    raise 'Failed storing record: #{vals}' if res.ntuples != 1
    return res.values[0]
  end

end
end	#module MyCHIPs
