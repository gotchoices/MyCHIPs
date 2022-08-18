import 'dart:ui';
import 'dart:collection';
import '../managers/user/account.dart';
import '../objects/key_storage.dart';
import '../objects/tally.dart';
import '../objects/transaction.dart';
import 'package:random_date/random_date.dart';

class AppContext {
  static final AppContext _instance = AppContext._internal();
  factory AppContext() {
    return _instance;
  }
  AppContext._internal();
  UserInfo? user;
}

class UserInfo {
  UserInfo() {
    //gets the user's personal key
    KeyStorage().readKeyValue().then((String value) {
      personalKey = value;
      showContact = false;
    });
    //TODO: Fetch transactions. For now statically put in these two, additionally we could just add this parameter into one of the other singletons
    Transaction tran1 = Transaction(RandomDate.withRange(2000, 2020).random(),
        "pizza", "John Doe", "You", 12);
    Transaction tran2 = Transaction(RandomDate.withRange(2000, 2020).random(),
        "wings", "you", "Jane Doe", 9);
    pendingTransactions.add(tran1);
    pendingTransactions.add(tran2);
  }

  double? userBalance;
  Map<String, double>? dataMap;
  List<Color>? colorList;
  Account? account;
  var showContact = false;
  var personalKey = "";
  var transactionList = HashMap<int, List<Transaction>>();
  var tallyList = <Tally>[];
  var pendingTransactions = <Transaction>[];
}
