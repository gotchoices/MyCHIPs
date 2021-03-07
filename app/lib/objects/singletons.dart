import 'dart:ui';
import 'dart:collection';
import 'package:flutter_app/objects/account.dart';
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
  Account account;
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

void initiateSingletons() {
  UserInfo();
  UserTransactions();
  UserTallies();
}
