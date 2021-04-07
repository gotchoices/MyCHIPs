import 'package:flutter_app/DAOs/transaction_dao.dart';

class TransactionPresenter {

  var dao = new TransactionDao();

  bool sendPayment(transaction) {
    print(transaction);
    dao.sendPayment(transaction);
    return false;
  }

  bool requestPayment(transaction) {
    print(transaction);
    dao.requestPayment(transaction);
    return false;
  }

  bool declinePayment(transaction) {
    dao.declineTransaction(transaction);
    return true;
  }

  bool cancelRequest(transaction) {
    dao.cancelRequest(transaction);
    return true;
  }

}