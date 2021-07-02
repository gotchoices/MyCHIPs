import 'package:flutter_app/DAOs/tally_page_dao.dart';
import 'package:flutter_app/objects/transaction.dart';

class TallyPagePresenter {
  var dao = new TallyPageDao();

  List<Transaction> getUserTransactions([Transaction lastTransaction, int numToFetch = 10]) {
    return dao.getUserTransactions(lastTransaction, numToFetch);
  }
}