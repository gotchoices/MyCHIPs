import 'dart:math';
import 'package:random_date/random_date.dart';

class Transaction {
  DateTime date;
  String sender;
  String receiver;
  var amount;

  Transaction(date, sender, receiver, amount) {
    this.date = date;
    this.sender = sender;
    this.receiver = receiver;
    this.amount = amount;
  }
}

class TransactionGenerator {
  static List<Transaction> generateFakeTransactions([numToGenerate = 10]) {
    var rng = new Random();
    List<Transaction> results = <Transaction>[];
    for (int i = 0; i < numToGenerate; i++) {
      Transaction t = new Transaction(
          RandomDate.withRange(2000, 2020).random(),
          "sender", "receiver",
          rng.nextInt(50) + rng.nextDouble() - 50);
      results.add(t);
    }
    return results;
  }
}