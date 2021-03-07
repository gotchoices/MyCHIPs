import 'package:flutter_app/DAOs/account_dao.dart';
import 'package:flutter_app/objects/account.dart';
import 'package:flutter_app/objects/singletons.dart';

class UserInfoPresenter {
  var dao = new AccountDao();

  Account getAccountData() {
    dao.getAccountData();
    return new Account(
        "TestUser", "Test", "User", "email@email.com", "123-123-1234");
  }

  void setAccountData(account) {
    UserInfo().account = account;
    dao.setAccountData(account);
  }
}
