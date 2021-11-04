//Test object list array functions
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
// TODO:
//- Maintain index to facilitate binary searches on object properties?
//- 
const assert = require("assert");
const ObjectSet = require("../../lib/objectset")
const array1 = [
  {a:1,	b:'hi', c:'John'},
  {a:3,	b:'ho', c:'Mary'},
  {a:7,	b:'hu', c:'Bill'},
]

function compare(v, o) {return (v == o.a)}

describe("Object sets", function() {
  var oSet1, element1, element2

  before('Create an object set', function() {
    oSet1 = new ObjectSet(array1)
  })

  it("Check for correct size", function() {
    assert.equal(oSet1.size(), 3)
  })

  it("Search for specified value", function() {
    element1 = oSet1.find(3, compare)
    assert.equal(element1.b, 'ho')
  })

  it("Delete specified value", function() {
    element1 = oSet1.find(3, compare)
    oSet1.delete(element1)
    assert.equal(oSet1.size(), 2)
    element1 = oSet1.find(1, compare)
    assert.equal(element1.b, 'hi')
    element2 = oSet1.find(7, compare)
    assert.equal(element2.b, 'hu')
  })

  it("Delete non-existant value", function() {
    element1 = oSet1.find(3, compare)
    oSet1.delete(element1)
    assert.equal(oSet1.size(), 2)
  })

  it("Add a new value", function() {
    oSet1.add({a:9,b:'ha',c:'Fred'})
    assert.equal(oSet1.size(), 3)
    element1 = oSet1.find('Fred', (v,o)=>(v == o.c))
    assert.equal(element1.b, 'ha')
  })

//  after('Clean up', function() {
//  })
});
