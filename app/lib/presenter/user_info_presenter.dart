import 'package:flutter_app/model/account_dao.dart';
import 'package:flutter_app/objects/account.dart';

class UserInfoPresenter {
  var dao = new AccountDao();

  Account getAccountInfo() {
    return new Account();
  }

  void setAccountInfo(account) {
    dao.setAccountData(account);
  }
}
