import 'package:flutter_app/objects/tally.dart';
import 'package:flutter_app/model/tally_list_dao.dart';

class TallyListPresenter {

  var dao = new TallyListDao();

  List<Tally> filterUsers(input, List<Tally>tallyList) {
    List<Tally> resultTallies = new List<Tally>();
    for (var i = 0; i < tallyList.length; i++) {
      Tally tempTally = tallyList[i];
      if (tempTally.friend.contains(input)) {
        resultTallies.add(tempTally);
      }
    }
    return resultTallies;
  }

  List<Tally> getUserTallies([Tally lastTally, int numToFetch = 10]) {
    return dao.getUserTallies(lastTally, numToFetch);
  }
}