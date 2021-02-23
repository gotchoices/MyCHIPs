import 'package:flutter_app/model/transaction_dao.dart';

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

}