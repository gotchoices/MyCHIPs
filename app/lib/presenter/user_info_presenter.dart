import 'package:flutter_app/DAOs/account_dao.dart';
import 'package:flutter_app/objects/account.dart';
import 'package:flutter_app/objects/singletons.dart';

class UserInfoPresenter {
  var dao = new AccountDao();

  Account getAccountData() {
    dao.getAccountData();
    return new Account(
        "ryle3", "Ryan", "Leach", "ryle3@byu.edu", "916-617-0471");
  }

  void setAccountData(account) {
    UserInfo().account = account;
    dao.setAccountData(account);
  }
}
