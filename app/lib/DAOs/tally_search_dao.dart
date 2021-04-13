import 'package:flutter_app/objects/tally.dart';
import 'package:flutter_app/objects/tally_generator.dart';

class TallySearchDao {
  List<Tally> getUserTallies([Tally lastTally, int numToFetch = 12]) {
    return TallyGenerator.generateFakeTallies(numToFetch);
  }
}
