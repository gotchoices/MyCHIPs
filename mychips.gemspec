Gem::Specification.new do |s|
  s.name        = 'MyCHIPs'
  s.version     = '0.10'
  s.date        = '2017-02-27'
  s.summary     = "Reference MyCHIPs server"
  s.description = "A server for exchanging privately issued time credits"
  s.authors     = ["Kyle Bateman"]
  s.email       = ["info@mychips.org"]
  s.platform    = Gem::Platform::RUBY
  s.files       = [
	"Copyright",
	"LICENSE",
	"README.md",
	"Release",
	"lib/mychips.rb",
	"schema/release-1.sql",
	"lib/mychips/crypto.rb",
	"lib/mychips/covenant.rb",
	"lib/mychips/db.rb",
	"bin/mc_peer",
	"bin/mc_admin",
	"bin/mc_user",
	"bin/mc_client"
]
  s.executables << 'mc_peer' << 'mc_user' << 'mc_client' << 'mc_admin'
  s.homepage    = 'http://gotchoices.org/mychips'
  s.requirements << 'Wyseman'
  s.license       = 'GPL-3.0'
end
