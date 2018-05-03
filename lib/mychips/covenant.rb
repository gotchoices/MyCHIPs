#!/bin/env ruby
#Parse, load, render contract covenants
#TODO:
#X- Add missing hash
#X- Fetch from URL
#- Fetch covenant from database
#- How to produce whole documents from covenant fragments
#- Render documents to html
#- Render documents to pdf
#- 

#require 'pg'
require 'openssl'
require 'nokogiri'
require 'net/http'
require 'uri'
require 'oj'

module MyCHIPs

# Read/process contract chunks, or covenants
# -----------------------------------------------------------------------------
class Covenant
  def initialize(cov)

    if cov =~ URI::regexp		#Is this a URL?
      @data = Oj.load(Net::HTTP.get(URI(cov)))
    elsif File::exist?(cov)		#Is this a file?
      Oj.default_options = {mode: :compat}
      @data = Oj.load(File.read(cov))
    else				#Look for a hash in the database
      raise "Can't find: #{cov}"
    end

    dig = OpenSSL::Digest::SHA256.new().digest(to_json(false,covenant)).unpack('H*')[0]
#printf("digest:%s:%s:%d\n", digest, dig, dig.length);
    if digest != dig			#Compare our computed digest to what is in the file
      raise "Recorded digest from: %s:\n  %s\ndoesn't match computed value:\n  %s\n" % [cov,digest,dig]
    end
  end

  def data
    @data
  end
  def covenant
    @data['covenant']
  end
  def digest
    @data['digest']
  end

# JSON outputter  
# -----------------------------------------------------------------------------
  def to_json(pretty = false, d = @data)
    Oj.default_options = Hash[mode: :strict, indent: (pretty ? 2 : 0)]
    Oj.dump(d)
  end

# XML outputter (broken)
# -----------------------------------------------------------------------------
  def to_xml()
    generate_xml(@data)
  end

#Source: http://stackoverflow.com/questions/11933451/converting-nested-hash-into-xml-using-nokogiri
# -----------------------------------------------------------------------------
  def generate_xml(data, parent = false, opt = {})	
    return if data.to_s.empty?
    return unless data.is_a?(Hash)

#printf("data:%s\nlen:%s\n", data,data.length)
    unless parent	# assume, if the hash has a single key, it should be the root
      root, data = (data.length == 1) ? data.shift : ["root", data]
      builder = Nokogiri::XML::Builder.new(opt) do |xml|
        xml.send(root) {
          generate_xml(data, xml)
        }
      end
      return builder.to_xml
    end

    data.each { |label, value|
#printf("label:%s value:%s\n", label.class, value.class)
      if value.is_a?(Hash)
        attrs = value.fetch('@attributes', {})
        text = value.fetch('@text', '')	#also passing 'text' as a key makes nokogiri do the same thing
        parent.send(label, attrs, text) { 
          value.delete('@attributes')
          value.delete('@text')
          generate_xml(value, parent)
        }
      elsif value.is_a?(Array)
        value.each { |el|
          el = {label => el}	# lets trick the above into firing so we do not need to rewrite the checks
          generate_xml(el, parent) 
        }
      else		#String
        parent.send(label.to_sym, value)	#Fixme: crashes if label = "hash"
      end
    }
  end	#generate_xml

end	#class Covenant
end	#module MyCHIPs

#Debug:
#ARGV.each_index {|x|		#Convert applicable arguments to symbols
#  ARGV[x] = ARGV[x][1..-1].to_sym if ARGV[x][0] == ':'
#  ARGV[x] = ARGV[x][0..-2].to_sym if ARGV[x][-1] == ':'
#}
#h = Hash[*ARGV]

c = MyCHIPs::Covenant.new(*ARGV)
#puts "XML:\n" + c.to_xml()
#puts "DATA:\n" + c.data()
puts 'JSON:' + c.to_json(false,c.covenant)
puts 'DIG:' + c.digest
