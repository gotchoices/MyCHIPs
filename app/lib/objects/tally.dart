import 'package:faker/faker.dart';
import 'dart:math';

class Tally {
  String friend;
  var balance;
  String host;
  String port;
  Tally(friend, balance) {
    this.friend = friend;
    this.balance = balance;
  }

  static Tally parseTallyTicket(ticket) {
    print(ticket.toString());
    return TallyGenerator.generateFakeTally();
  }
}

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
