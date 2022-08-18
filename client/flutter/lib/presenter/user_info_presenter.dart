import '../DAOs/account_dao.dart';
import '../managers/user/account.dart';
import '../objects/singletons.dart';

class UserInfoPresenter {
  var dao = new AccountDao();

  Account getAccountData() {
    dao.getAccountData();
    return new Account("ryle3", "Ryan", "Leach",
        email: "ryle3@byu.edu", phone: "916-617-0471");
  }

  void setAccountData(account) {
    UserInfo().account = account;
    dao.setAccountData(account);
  }
}
