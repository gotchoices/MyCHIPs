#Test signature validation inside database
#Copyright MyCHIPs.org; See license in root of this package
# -----------------------------------------------------------------------------
#Dependencies
# dnf install postgresql-python
# pip install rsa
#
#For plv8:
# wget https://github.com/plv8/plv8/archive/v2.3.13.tar.gz
# tar -xvzf v2.3.13.tar.gz
# cd plv8-2.3.13
# make

data.txt:
	echo -n "Here is some test data." >data.txt

#Generate private key. Provide secure passphrase when prompted.
private.pem:
	openssl genrsa -out private.pem 2048	#-aes256 

#Export public KEY
public.pem: private.pem
	openssl rsa -in private.pem -pubout -out public.pem	#-RSAPublicKey_out 

#Sign data. Provide secure passphrase when prompted.
#Remove first line (RSA-SHA256(data.txt)=) when passing into database verify function.
#openssl dgst -sha256 -sign private.pem -out sign.bin data.txt
#openssl hex -in sign.bin -out signature.txt
signature.txt: data.txt private.pem
	openssl dgst -hex -sign private.pem -out signature.txt data.txt

#Test validata the data
#openssl hex -d -in signature.txt -out sign.bin
sign.hex: signature.txt
	sed <signature.txt -e 's/RSA.*= \(.*\)$$/\1/' >sign.hex

sign.bin: sign.hex
	cat sign.hex |xxd -r -p >sign.bin

verify: public.pem sign.bin
	openssl dgst -sha256 -verify public.pem -signature sign.bin data.txt

#Test our function:
test: data.txt sign.hex public.pem
	psql mychips admin -c "select mychips.validate('$(cat data.txt)','$(cat sign.hex)','$(cat public.pem)')"

clean:
	rm -f public.pem private.pem signature.txt sign.hex sign.bin data.txt
