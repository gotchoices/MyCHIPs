import 'package:faker/faker.dart';
import 'package:flutter_app/objects/singletons.dart';
import 'package:flutter_app/objects/account.dart';
import 'package:flutter_app/objects/transaction.dart';
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
    Tally houseTally = new Tally(new Account("AmericanExpress", "House Mortgage", "",),  -50);
    tallyList.add(houseTally);
    transactionList[202] = [Transaction(
        DateTime(2010), "House Loan", "House Mortgage", "ryle3", -1000), Transaction(
        DateTime(2011), "first year payment", "ryle3", "House Mortgage", 100), Transaction(
        DateTime(2012), "second year payment", "ryle3", "House Mortgage", 100), Transaction(
        DateTime(2013), "third year payment", "ryle3", "House Mortgage", 100), Transaction(
        DateTime(2014), "fourth year payment", "ryle3", "House Mortgage", 100), Transaction(
        DateTime(2015), "fifth year payment", "ryle3", "House Mortgage", 100), Transaction(
        DateTime(2016), "sixth year payment", "ryle3", "House Mortgage", 100), Transaction(
        DateTime(2017), "seventh year payment", "ryle3", "House Mortgage", 100), Transaction(
        DateTime(2018), "eighth year payment", "ryle3", "House Mortgage", 100), Transaction(
        DateTime(2019), "ninth year payment", "ryle3", "House Mortgage", 100), Transaction(
        DateTime(2020), "tenth year payment", "ryle3", "House Mortgage", 50) ];
    results.add(houseTally);

    return results;
  }

  static Tally generateFakeTally() {
    var rng = new Random();
    var faker =  new Faker();
    return new Tally(
        new Account(faker.person.name(), faker.person.firstName(), faker.person.lastName()),
        num.parse((rng.nextInt(100) + rng.nextDouble() - 50).toStringAsFixed(2))
    );
  }
}