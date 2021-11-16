// A place for our tests!
const assert = require("assert");

describe("Example Tests", function() {
    it("Make sure math works...", function() {
        assert.equal(42, 21 * 2)
    })
    it("What happen when a test fails?", function() {
        assert.equal(13 - 2, 10)
    })
})