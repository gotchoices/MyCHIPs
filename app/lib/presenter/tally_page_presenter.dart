import '../DAOs/tally_page_dao.dart';
import '../objects/transaction.dart';

class TallyPagePresenter {
  var dao = new TallyPageDao();

  List<Transaction> getUserTransactions(
      [Transaction? lastTransaction, int numToFetch = 10]) {
    return dao.getUserTransactions(lastTransaction, numToFetch);
  }
}
