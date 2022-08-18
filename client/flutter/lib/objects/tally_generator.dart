import 'package:faker/faker.dart';
import '../objects/singletons.dart';
import '../managers/user/account.dart';
import '../objects/transaction.dart';
import '../objects/transaction_generator.dart';
import 'dart:math';
import 'tally.dart';

class TallyGenerator {
  static List<Tally> generateFakeTallies([numToGenerate = 12]) {
    List<Tally> results = <Tally>[];
    var user = AppContext().user;
    if (user != null) {
      var transactionList = user.transactionList;
      var tallyList = user.tallyList;
      for (int i = 0; i < numToGenerate; i++) {
        Tally t = generateFakeTally();
        tallyList.add(t);
        transactionList[t.personID] =
            TransactionGenerator.generateFakeTransactions();
        results.add(t);
      }

      Tally houseTally = Tally(
          Account(
            "American Express",
            "",
            "",
          ),
          -50);
      tallyList.add(houseTally);
      transactionList[houseTally.personID] = [
        Transaction(DateTime(2010), "", "American Express", "ryle3", 1150),
        Transaction(DateTime(2011), "", "American Express", "ryle3", -100),
        Transaction(DateTime(2012), "", "American Express", "ryle3", -100),
        Transaction(DateTime(2013), "", "American Express", "ryle3", -100),
        Transaction(DateTime(2014), "", "American Express", "ryle3", -100),
        Transaction(DateTime(2015), "", "American Express", "ryle3", -100),
        Transaction(DateTime(2016), "", "American Express", "ryle3", -100),
        Transaction(DateTime(2017), "", "American Express", "ryle3", -100),
        Transaction(DateTime(2018), "", "American Express", "ryle3", -100),
        Transaction(DateTime(2019), "", "American Express", "ryle3", -100),
        Transaction(DateTime(2020), "", "American Express", "ryle3", -100),
        Transaction(DateTime(2021), "", "American Express", "ryle3", -100)
      ];
      results.add(houseTally);

      Tally investingTally = Tally(Account("Robin Hood", "", ""), -50);
      tallyList.add(investingTally);
      transactionList[investingTally.personID] = [
        Transaction(DateTime(2021, 1, 20), "", "Robin Hood", "ryle3", -20),
        Transaction(DateTime(2021, 2, 5), "", "Robin Hood", "ryle3", 100),
        Transaction(DateTime(2021, 2, 7), "", "Robin Hood", "ryle3", -80),
        Transaction(DateTime(2021, 3, 10), "", "Robin Hood", "ryle3", 20),
        Transaction(DateTime(2021, 3, 11), "", "Robin Hood", "ryle3", -20),
        Transaction(DateTime(2021, 4, 11), "", "Robin Hood", "ryle3", 30)
      ];
      results.add(investingTally);

      Tally jobTally = Tally(Account("Kyle Bateman", "", ""), 100);
      tallyList.add(jobTally);
      transactionList[jobTally.personID] = [
        Transaction(DateTime(2020, 11, 20), "", "Kyle Bateman", "ryle3", 20),
        Transaction(DateTime(2020, 12, 20), "", "Kyle Bateman", "ryle3", 20),
        Transaction(DateTime(2021, 1, 20), "", "Kyle Bateman", "ryle3", 20),
        Transaction(DateTime(2021, 2, 20), "", "Kyle Bateman", "ryle3", 20),
        Transaction(DateTime(2021, 3, 20), "", "Kyle Bateman", "ryle3", 20)
      ];
      results.add(jobTally);

      Tally sideHustleTally = Tally(Account("Ryan's T-Shirts", "", ""), 50);
      tallyList.add(sideHustleTally);
      transactionList[sideHustleTally.personID] = [
        Transaction(
            DateTime(2020, 11, 20), "", "Ryan's T-Shirts", "ryle3", -50),
        Transaction(DateTime(2020, 12, 20), "", "Ryan's T-Shirts", "ryle3", 25),
        Transaction(DateTime(2021, 1, 20), "", "Ryan's T-Shirts", "ryle3", 25),
        Transaction(DateTime(2021, 2, 20), "", "Ryan's T-Shirts", "ryle3", 25),
        Transaction(DateTime(2021, 3, 20), "", "Ryan's T-Shirts", "ryle3", 25)
      ];
      results.add(sideHustleTally);
    }
    return results;
  }

  static Tally generateFakeTally() {
    var rng = Random();
    var faker = Faker();
    return Tally(
        Account(faker.person.name(), faker.person.firstName(),
            faker.person.lastName()),
        num.parse(
            (rng.nextInt(100) + rng.nextDouble() - 50).toStringAsFixed(2)));
  }
}
