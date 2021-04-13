import 'dart:ui';
import 'dart:collection';
import 'package:flutter_app/objects/account.dart';
import 'package:flutter_app/objects/key_storage.dart';
import 'package:flutter_app/objects/tally.dart';
import 'package:flutter_app/objects/transaction.dart';
import 'package:random_date/random_date.dart';

class UserInfo {
  static UserInfo _instance;

  UserInfo._internal() {
    _instance = this;
    //gets the user's personal key
    new KeyStorage().readKeyValue().then((String value) {
        personalKey = value;
        showContact = false;
    });
  }

  factory UserInfo() => _instance ?? UserInfo._internal();

  double userBalance;
  Map<String, double> dataMap;
  List<Color> colorList;
  Account account;
  bool showContact;
  String personalKey;
}

class UserTransactions {
  static UserTransactions _instance;

  UserTransactions._internal() {
    _instance = this;
  }

  factory UserTransactions() => _instance ?? UserTransactions._internal();
  HashMap transactionList = new HashMap<int, List<Transaction>>();
}

class UserTallies {
  static UserTallies _instance;

  UserTallies._internal() {
    _instance = this;
  }

  factory UserTallies() => _instance ?? UserTallies._internal();
  List tallyList = <Tally>[];
}

class PendingTransactions {
  static PendingTransactions _instance;

  PendingTransactions._internal() {
    _instance = this;
    //TODO: Fetch transactions. For now statically put in these two, additionally we could just add this parameter into one of the other singletons
    Transaction tran1 = Transaction(RandomDate.withRange(2000, 2020).random(),
        "pizza", "John Doe", "You", 12);
    Transaction tran2 = Transaction(
        RandomDate.withRange(2000, 2020).random(), "wings", "you", "Jane Doe", 9);
    transactionList.add(tran1);
    transactionList.add(tran2);
  }
  factory PendingTransactions() => _instance ?? PendingTransactions._internal();
  List transactionList = <Transaction>[];
}

void initiateSingletons() {
  UserInfo();
  UserTransactions();
  UserTallies();
  PendingTransactions();
}
