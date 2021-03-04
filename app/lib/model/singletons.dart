import 'dart:ui';

import 'package:flutter_app/objects/tally.dart';
import 'package:flutter_app/objects/transaction.dart';

class UserInfo {
  static UserInfo _instance;

  UserInfo._internal() {
    _instance = this;
  }

  factory UserInfo() => _instance ?? UserInfo._internal();

  double userBalance;
  Map<String, double> dataMap;
  List<Color> colorList;
}

class UserTransactions {
  static UserTransactions _instance;

  UserTransactions._internal() {
    _instance = this;
  }

  factory UserTransactions() => _instance ?? UserTransactions._internal();
  List transactionList = <Transaction>[];
  int checkedIndex;
  int markedIndex;
}

class UserTallies {
  static UserTallies _instance;

  UserTallies._internal() {
    _instance = this;
  }

  factory UserTallies() => _instance ?? UserTallies._internal();
  List tallyList = <Tally>[];
}

void initiateSingletons() {
  UserInfo();
  UserTransactions();
  UserTallies();
}
