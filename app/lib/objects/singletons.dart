import 'dart:ui';
import 'dart:collection';
import 'package:flutter_app/objects/account.dart';
import 'package:flutter_app/objects/key_storage.dart';
import 'package:flutter_app/objects/tally.dart';
import 'package:flutter_app/objects/transaction.dart';

class UserInfo {
  static UserInfo _instance;

  UserInfo._internal() {
    _instance = this;
    //gets the user's personal key
    new KeyStorage().readKeyValue().then((String value) {
        personalKey = value;
    });
  }

  factory UserInfo() => _instance ?? UserInfo._internal();

  double userBalance;
  Map<String, double> dataMap;
  List<Color> colorList;
  Account account;
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

void initiateSingletons() {
  UserInfo();
  UserTransactions();
  UserTallies();
}
