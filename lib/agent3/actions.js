/* Interface
  This actions interface should only be used as a blueprint when designing other actions.
*/

class Actions {
  shouldProcess() {
    throw "must implement shouldProcess() for 'Actions' type classes. Returns a boolean of whether criteria have been met"
  }

  process() {
    throw "must implement process() for 'Actions' type classes"
  }
}
