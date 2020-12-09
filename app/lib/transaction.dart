import 'dart:math';
import 'package:random_date/random_date.dart';

class Transaction {
  DateTime date;
  String sender;
  String receiver;
  String message;
  var amount;

  Transaction(date, message, sender, receiver, amount) {
    this.date = date;
    this.message = message;
    this.sender = sender;
    this.receiver = receiver;
    this.amount = amount;
  }
}

class TransactionGenerator {
  static List<Transaction> generateFakeTransactions([numToGenerate = 10]) {
    List<Transaction> results = <Transaction>[];
    for (int i = 0; i < numToGenerate; i++) {
      Transaction t = generateFakeTransation();
      results.add(t);
    }
    return results;
  }

  static generateFakeTransation() {
    var rng = new Random();
    return Transaction(
        RandomDate.withRange(2000, 2020).random(),
        "fake message", "sender", "receiver",
        rng.nextInt(50) + rng.nextDouble() - 50);
  }
}