import 'package:flutter_app/model/account_dao.dart';
import 'package:flutter_app/objects/account.dart';

class UserInfoPresenter {
  var dao = new AccountDao();

  Account getAccountInfo() {
    return new Account(
        "TestUser", "Test", "User", "email@email.com", "123-123-1234");
  }

  void setAccountInfo(account) {
    dao.setAccountData(account);
  }
}
