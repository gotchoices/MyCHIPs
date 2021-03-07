import 'package:flutter_app/DAOs/transaction_dao.dart';

class TransactionPresenter {

  var dao = new TransactionDao();

  bool sendPayment(transaction) {
    dao.sendPayment(transaction);
    return false;
  }

  bool requestPayment(transaction) {
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