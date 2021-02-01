import 'package:flutter_app/model/transaction_dao.dart';

class TransactionPresenter {

  var dao = new TransactionDao();

  bool sendPayment(transaction) {
    dao.sendPayment(transaction);
  }

  bool requestPayment(transaction) {
    dao.requestPayment(transaction);
  }

}