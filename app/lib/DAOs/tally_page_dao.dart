import '../objects/transaction.dart';
import '../objects/transaction_generator.dart';

class TallyPageDao {
  List<Transaction> getUserTransactions(
      [Transaction? lastTransaction, int numToFetch = 10]) {
    return TransactionGenerator.generateFakeTransactions(numToFetch);
  }
}
