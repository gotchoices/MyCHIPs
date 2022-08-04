import 'package:rxdart/rxdart.dart';

import 'account.dart';

class UserManager {
  static final UserManager _instance = UserManager._internal();
  factory UserManager() {
    return _instance;
  }
  UserManager._internal();

  final accountSubject = BehaviorSubject<Account>();

  void SetAccount(Account account) {
    accountSubject.sink.add(account);
  }
}
