import '../objects/tally.dart';
import '../DAOs/tally_search_dao.dart';

class TallySearchPresenter {
  var dao = new TallySearchDao();

  List<Tally> filterUsers(input, List<Tally> tallyList) {
    List<Tally> resultTallies = [];
    for (var i = 0; i < tallyList.length; i++) {
      Tally tempTally = tallyList[i];
      if (tempTally.friend?.displayName
              .toLowerCase()
              .contains(input.toString().toLowerCase()) ??
          false) {
        resultTallies.add(tempTally);
      }
    }
    return resultTallies;
  }

  List<Tally> getUserTallies([Tally? lastTally, int numToFetch = 12]) {
    return dao.getUserTallies(lastTally, numToFetch);
  }
}
