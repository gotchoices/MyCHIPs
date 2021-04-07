import 'package:faker/faker.dart';
import 'package:flutter_app/objects/singletons.dart';
import 'package:flutter_app/objects/account.dart';
import 'package:flutter_app/objects/transaction_generator.dart';
import 'dart:math';
import 'tally.dart';

class TallyGenerator {
  static List<Tally> generateFakeTallies([numToGenerate = 12]) {
    Map transactionList = UserTransactions().transactionList;
    List<Tally> tallyList = UserTallies().tallyList;
    List<Tally> results = <Tally>[];
    for (int i = 0; i < numToGenerate; i++) {
      Tally t = generateFakeTally();
      tallyList.add(t);
      transactionList[t.personID] = TransactionGenerator.generateFakeTransactions();
      results.add(t);
    }
    return results;
  }

  static Tally generateFakeTally() {
    var rng = new Random();
    var faker =  new Faker();
    return new Tally(
        new Account(faker.person.name(), faker.person.firstName(), faker.person.lastName()),
        rng.nextInt(100)
    );
  }
}