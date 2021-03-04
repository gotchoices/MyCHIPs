import 'dart:math';
import 'package:random_date/random_date.dart';
import 'transaction.dart';

class TransactionGenerator {
  static List<Transaction> generateFakeTransactions([numToGenerate = 10]) {
    List<Transaction> results = <Transaction>[];
    for (int i = 0; i < numToGenerate; i++) {
      Transaction t = generateFakeTransaction();
      results.add(t);
    }
    return results;
  }

  static generateFakeTransaction() {
    var rng = new Random();
    return Transaction(
        RandomDate.withRange(2000, 2020).random(),
        "fake message", "sender", "receiver",
        rng.nextInt(50) + rng.nextDouble() - 50);
  }
}