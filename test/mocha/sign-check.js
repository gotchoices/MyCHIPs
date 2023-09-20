const assert = require('assert');
const crypto = require('crypto');
const WebCrypto = require('crypto').webcrypto;
const Subtle = WebCrypto.subtle
const sinon = require('sinon');

const TallyCrypto = require('../../lib/crypto.js')

const fakeKeyObject = {
  "publicKey": {
      "key_ops": [
          "verify"
      ],
      "ext": true,
      "kty": "EC",
      "x": "APuNNFFOQ6gu3rqnd7xlx_pfj_aZ632rFDAhY_otEhHMyZnpWJjLw0NaLzzkfpWzRvZK48tb2zmDi_9CUFJbymcZ",
      "y": "Af_5EACD6KzKueAZH8Xcpng4J5Jf3PHdMxQ0ZOpw9hNEFy_cDAoG2Yb18VWxxE36lvddiuOxJxwHIsmJvX1G11uk",
      "crv": "P-521"
  },
  "privateKey": {
      "key_ops": [
          "sign"
      ],
      "ext": true,
      "kty": "EC",
      "x": "APuNNFFOQ6gu3rqnd7xlx_pfj_aZ632rFDAhY_otEhHMyZnpWJjLw0NaLzzkfpWzRvZK48tb2zmDi_9CUFJbymcZ",
      "y": "Af_5EACD6KzKueAZH8Xcpng4J5Jf3PHdMxQ0ZOpw9hNEFy_cDAoG2Yb18VWxxE36lvddiuOxJxwHIsmJvX1G11uk",
      "crv": "P-521",
      "d": "Afiv6yQkIMoz_i-WrnV4jJLCqHAFLlavgjp-fm5hbpghmq_5Se3WnoW9OZy2rEs6NMzfz4orl4QcxgwB0lylQpvQ"
  }
};


describe('TallyCrypto Class', () => {
  describe('Generate method', () => {
    it('Should generate key pair and call the callback with keys', (done) => {
      const tallyCrypto = new TallyCrypto(console);

      tallyCrypto.generate((keys, priv, publ) => {
        assert.strictEqual(typeof keys, 'object'); // publicKey should be an object
        assert.strictEqual(keys.publicKey.type, 'public'); // publicKey should have type "public"
        assert.strictEqual(keys.publicKey.extractable, true); // publicKey should be extractable
        assert.deepStrictEqual(keys.publicKey.algorithm, { name: 'ECDSA', namedCurve: 'P-521' }); // publicKey algorithm should match
        assert.deepStrictEqual(keys.publicKey.usages, ['verify']); // publicKey usages should include "verify"
        assert.strictEqual(typeof keys.privateKey, 'object'); // privateKey should be an object
        assert.strictEqual(keys.privateKey.type, 'private'); // privateKey should have type "private"
        assert.strictEqual(keys.privateKey.extractable, true); // privateKey should be extractable
        assert.deepStrictEqual(keys.privateKey.algorithm, { name: 'ECDSA', namedCurve: 'P-521' }); // privateKey algorithm should match
        assert.deepStrictEqual(keys.privateKey.usages, ['sign']); // privateKey usages should include "sign"
        assert.strictEqual(typeof priv, 'object'); // priv should be an object
        assert.deepStrictEqual(priv.key_ops, ['sign']); // key_ops should be ["sign"]
        assert.strictEqual(priv.ext, true); // ext should be true
        assert.strictEqual(priv.kty, 'EC'); // kty should be "EC"
        assert.strictEqual(typeof priv.x, 'string'); // x should be a string
        assert.strictEqual(typeof priv.y, 'string'); // y should be a string
        assert.strictEqual(priv.crv, 'P-521'); // crv should be "P-521"
        assert.strictEqual(typeof priv.d, 'string'); // d should be a string
        assert.strictEqual(typeof publ, 'object');
        assert.strictEqual(typeof publ, 'object'); // publ should be an object
        assert.deepStrictEqual(publ.key_ops, ['verify']); // key_ops should be ["verify"]
        assert.strictEqual(publ.ext, true); // ext should be true
        assert.strictEqual(publ.kty, 'EC'); // kty should be "EC"
        assert.strictEqual(typeof publ.x, 'string'); // x should be a string
        assert.strictEqual(typeof publ.y, 'string'); // y should be a string
        assert.strictEqual(publ.crv, 'P-521'); // crv should be "P-521"
        done()
      });


    });

    it('should handle errors gracefully and call the error log', (done) => {
      const error = new Error('Test error');
      const subtleStub = sinon.stub(Subtle, 'generateKey').rejects(error);
      const logErrorStub = sinon.stub(console, 'error');
      const tallyCrypto = new TallyCrypto(console);

      tallyCrypto.generate((keys, priv, publ) => {
        assert.strictEqual(keys, undefined);
        assert.strictEqual(priv, undefined);
        assert.strictEqual(publ, undefined);
        subtleStub.restore();
        done()
      });
    });
  });


  describe('Sign method', () => {
    it('should sign a message and call the callback with the signature for string key', (done) => {
      const tallyCrypto = new TallyCrypto(console);
      const fakeKeyString = JSON.stringify(fakeKeyObject.privateKey);
      const fakeSignature = crypto.randomBytes(64);
      const fakeMessage = 'Test message';

      const importKeyStub = sinon.stub(Subtle, 'importKey').resolves(fakeKeyObject.privateKey);
      const signStub = sinon.stub(Subtle, 'sign').resolves(fakeSignature);

      tallyCrypto.sign(fakeKeyString, fakeMessage, (signature) => {
        assert.deepStrictEqual(signature, fakeSignature);
        importKeyStub.restore();
        signStub.restore();
        done();
      });
    });

    it('should sign a message and call the callback with the signature for JSON key', (done) => {
      const tallyCrypto = new TallyCrypto(console);
      const fakeSignature = crypto.randomBytes(64);
      const fakeMessage = 'Test message';

      const importKeyStub = sinon.stub(Subtle, 'importKey').resolves(fakeKeyObject.privateKey);
      const signStub = sinon.stub(Subtle, 'sign').resolves(fakeSignature);

      tallyCrypto.sign(fakeKeyObject.privateKey, fakeMessage, (signature) => {
        assert.deepStrictEqual(signature, fakeSignature);
        importKeyStub.restore();
        signStub.restore();
        done();
      });
    });

    it('should sign a message object and call the callback with the signature', (done) => {
      const tallyCrypto = new TallyCrypto(console);
      const fakeSignature = crypto.randomBytes(64);
      const fakeMessage = { message: 'Test message', date: Date.now()};

      const importKeyStub = sinon.stub(Subtle, 'importKey').resolves(fakeKeyObject.privateKey);
      const signStub = sinon.stub(Subtle, 'sign').resolves(fakeSignature);

      tallyCrypto.sign(fakeKeyObject.privateKey, fakeMessage, (signature) => {
        assert.deepStrictEqual(signature, fakeSignature);
        importKeyStub.restore();
        signStub.restore();
        done();
      });
    });

    it('should handle errors gracefully and call the error log', (done) => {
      const tallyCrypto = new TallyCrypto(console);
      const fakeMessage = 'Test message';

      const error = new Error('Test error');
      const importKeyStub = sinon.stub(Subtle, 'importKey').rejects(error);

      tallyCrypto.sign(fakeKeyObject.privateKey, fakeMessage, (signature, err) => {
        assert.strictEqual(signature, null);
        importKeyStub.restore();
        done();
      });
    });
  });

  describe('verify', () => {
    it('should verify a valid signature and call the callback with true', (done) => {
      const tallyCrypto = new TallyCrypto(console);
      const fakeSignature = crypto.randomBytes(64);
      const fakeMessage = 'Test message';

      const importKeyStub = sinon.stub(Subtle, 'importKey').resolves(fakeKeyObject.publicKey);
      const verifyStub = sinon.stub(Subtle, 'verify').resolves(true);

      tallyCrypto.verify(fakeKeyObject.publicKey, fakeMessage, fakeSignature, (isValid) => {
        assert.strictEqual(isValid, true);
        importKeyStub.restore();
        verifyStub.restore();
        done();
      });
    });

    it('should verify an invalid signature and call the callback with false', (done) => {
      const tallyCrypto = new TallyCrypto(console);
      const fakeSignature = crypto.randomBytes(64);
      const fakeMessage = 'Test message';

      const importKeyStub = sinon.stub(Subtle, 'importKey').resolves(fakeKeyObject.privateKey);
      const verifyStub = sinon.stub(Subtle, 'verify').resolves(false);

      tallyCrypto.verify(fakeKeyObject.privateKey, fakeMessage, fakeSignature, (isValid) => {
        assert.strictEqual(isValid, false);
        importKeyStub.restore();
        verifyStub.restore();
        done();
      });
    });

    it('sould handle string and object argments', (done) => {
      const tallyCrypto = new TallyCrypto(console);
      const fakeKeyString = JSON.stringify(fakeKeyObject.publicKey);
      const fakeMessage = {message:'Test message'};
      const fakeSignature = crypto.randomBytes(64).toString('base64url');

      const importKeyStub = sinon.stub(Subtle, 'importKey').resolves(fakeKeyObject.publicKey);
      const verifyStub = sinon.stub(Subtle, 'verify').resolves(true);

      tallyCrypto.verify(fakeKeyString, fakeMessage, fakeSignature, (isValid) => {
        assert.strictEqual(isValid, true);
        importKeyStub.restore();
        verifyStub.restore();
        done();
      });
    })

    it('should handle errors gracefully and call the error log', (done) => {
      const tallyCrypto = new TallyCrypto(console);
      const fakeSignature = crypto.randomBytes(64);
      const error = new Error('Test error');
      const fakeMessage = 'Test message';
      const importKeyStub = sinon.stub(Subtle, 'importKey').rejects(error);

      tallyCrypto.verify(fakeKeyObject.publicKey, fakeMessage, fakeSignature, (isValid, err) => {
        assert.strictEqual(isValid, null);
        assert.strictEqual(err.message, error.message);
        importKeyStub.restore();
        done();
      });
    });
  });
});