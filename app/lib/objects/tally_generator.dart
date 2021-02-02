import 'package:faker/faker.dart';
import 'dart:math';
import 'tally.dart';

class TallyGenerator {
  static List<Tally> generateFakeTallies([numToGenerate = 10]) {
    List<Tally> results = <Tally>[];
    for (int i = 0; i < numToGenerate; i++) {
      Tally t = generateFakeTally();
      results.add(t);
    }
    return results;
  }

  static Tally generateFakeTally() {
    var rng = new Random();
    var faker =  new Faker();
    return new Tally(
        faker.person.name(),
        rng.nextInt(100)
    );
  }
}