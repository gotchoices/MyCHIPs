import 'package:flutter_app/objects/tally.dart';
import 'package:flutter_app/model/tally_list_dao.dart';

class TallyListPresenter {

  var dao = new TallyListDao();

  void filterUsers(input) {
    //TODO: logic to filter searched users here
    print(input);
  }

  List<Tally> getUserTallies([Tally lastTally, int numToFetch = 10]) {
    return dao.getUserTallies(lastTally, numToFetch);
  }
}