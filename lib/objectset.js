//Maintain sets of objects
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
// TODO:
//- Could keep list sorted for faster binary search lookups
//- 

module.exports = class ObjectSet {
  constructor(contents) {
    this.set = new Set()
    if (contents) contents.forEach(c => {
      this.set.add(c)
    })
  }

  size() {
    return this.set.size
  }
  
  add(element) {
    return this.set.add(element)
  }

  find(value, compare = (a,b)=>(a==b)) {	//---- Search for an object in the array
    if (value) for (let element of this.set) {
//console.log("el:", value, element)
      if (compare(value, element))
        return element
    }
    return undefined
  }

  delete(element) {				//---- Remove an object from the array
    this.set.delete(element)
  }
  
}		//class ObjectList
