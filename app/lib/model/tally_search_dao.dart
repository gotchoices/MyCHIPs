import 'package:flutter_app/objects/tally.dart';
import 'package:flutter_app/objects/tally_generator.dart';

class TallySearchDao {
  List<Tally> getUserTallies([Tally lastTally, int numToFetch = 10]) {
    // if (lastTally == null) return fromTheStart;
    return TallyGenerator.generateFakeTallies(numToFetch);
  }
}
