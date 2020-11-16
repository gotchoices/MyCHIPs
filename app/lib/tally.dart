import 'package:faker/faker.dart';
import 'dart:math';

class Tally {
  String friend;
  var balance;
  Tally(friend, balance)
  {
    this.friend = friend;
    this.balance = balance;
  }
}

class TallyGenerator {
  static List<Tally> generateFakeTallies([numToGenerate = 10])
  {
    var rng = new Random();
    List<Tally> results = <Tally>[];
    for (int i = 0; i < numToGenerate; i++)
    {
      var faker =  new Faker();
      Tally t = new Tally(
          faker.person.name(),
          rng.nextInt(100)
      );
      results.add(t);
    }
    return results;
  }
}